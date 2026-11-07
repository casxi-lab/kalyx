//! Sorting and searching lists of terms in the total order, charged.
//!
//! The constructors collect factors and monomials in the order in which they
//! meet them and sort the collection afterwards, with a bottom-up merge sort
//! over the positions of the items: every comparison is a charged comparison
//! of terms, and every item placed by a merge step charges one unit. Sorting
//! $n$ items takes $O(n \log n)$ comparisons, and no step moves more than one
//! position.

use std::cmp::Ordering;

use crate::{Context, Result};

use super::Term;
use super::node::internal;
use super::order;

/// An item that is sorted by a term and a sign: by the term in the total
/// order, then the item without the sign before the item with it.
pub(super) trait SortItem {
    /// The term that orders the item.
    fn sort_term(&self) -> &Term;
    /// Whether the item carries the sign; an item with the sign comes after
    /// an item with an equal term without it.
    fn sort_negative(&self) -> bool;
}

impl SortItem for Term {
    fn sort_term(&self) -> &Term {
        self
    }

    fn sort_negative(&self) -> bool {
        false
    }
}

/// The order of two items: their terms, then their signs.
pub(super) fn compare_items<T: SortItem>(
    left: &T,
    right: &T,
    context: &mut Context,
) -> Result<Ordering> {
    let by_term = order::compare(left.sort_term(), right.sort_term(), context)?;
    match by_term {
        Ordering::Equal => Ok(order_signs(left.sort_negative(), right.sort_negative())),
        Ordering::Less | Ordering::Greater => Ok(by_term),
    }
}

/// Two signs: the item without the sign first.
const fn order_signs(left: bool, right: bool) -> Ordering {
    if left == right {
        Ordering::Equal
    } else if right {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

/// The positions of `items` in ascending order; equal items keep their
/// relative order.
pub(super) fn sorted_order<T: SortItem>(items: &[T], context: &mut Context) -> Result<Vec<usize>> {
    let mut positions = identity(items.len());
    let mut width: usize = 1;
    while width < items.len() {
        positions = merge_pass(items, &positions, width, context)?;
        width = width.saturating_mul(2);
    }
    Ok(positions)
}

/// The positions `0..length`.
fn identity(length: usize) -> Vec<usize> {
    let mut positions = Vec::with_capacity(length);
    let mut index = 0;
    while index < length {
        positions.push(index);
        index += 1;
    }
    positions
}

/// One pass of the merge sort: merges each pair of neighboring runs of
/// `width` positions.
fn merge_pass<T: SortItem>(
    items: &[T],
    positions: &[usize],
    width: usize,
    context: &mut Context,
) -> Result<Vec<usize>> {
    let mut merged = Vec::with_capacity(positions.len());
    let mut start = 0;
    while start < positions.len() {
        let middle = advance(start, width, positions.len());
        let end = advance(middle, width, positions.len());
        merge_runs(items, positions, (start, middle, end), &mut merged, context)?;
        start = end;
    }
    Ok(merged)
}

/// `start + width`, but at most `length`; `start` is at most `length`.
const fn advance(start: usize, width: usize, length: usize) -> usize {
    if width > length - start {
        length
    } else {
        start + width
    }
}

/// Merges the sorted runs `start..middle` and `middle..end` of `positions`
/// onto `merged`, charging one unit per position placed.
fn merge_runs<T: SortItem>(
    items: &[T],
    positions: &[usize],
    run: (usize, usize, usize),
    merged: &mut Vec<usize>,
    context: &mut Context,
) -> Result<()> {
    let (start, middle, end) = run;
    let mut left = start;
    let mut right = middle;
    while left < middle || right < end {
        context.charge(1)?;
        let from_left = takes_left(items, positions, (left, middle, right, end), context)?;
        let next = if from_left { left } else { right };
        merged.push(position_at(positions, next)?);
        if from_left {
            left += 1;
        } else {
            right += 1;
        }
    }
    Ok(())
}

/// Whether the next position comes from the left run: when the right run is
/// used up, or when the left item is not greater than the right one.
fn takes_left<T: SortItem>(
    items: &[T],
    positions: &[usize],
    cursors: (usize, usize, usize, usize),
    context: &mut Context,
) -> Result<bool> {
    let (left, middle, right, end) = cursors;
    if left >= middle {
        return Ok(false);
    }
    if right >= end {
        return Ok(true);
    }
    let order = compare_items(
        item_at(items, positions, left)?,
        item_at(items, positions, right)?,
        context,
    )?;
    Ok(order != Ordering::Greater)
}

/// The position `positions[index]`.
fn position_at(positions: &[usize], index: usize) -> Result<usize> {
    match positions.get(index) {
        Some(position) => Ok(*position),
        None => Err(internal("a merge step outside its runs")),
    }
}

/// The item at position `positions[index]` of `items`.
pub(super) fn item_at<'a, T>(items: &'a [T], positions: &[usize], index: usize) -> Result<&'a T> {
    match positions.get(index) {
        Some(position) => match items.get(*position) {
            Some(item) => Ok(item),
            None => Err(internal("a sorted position outside its list")),
        },
        None => Err(internal("a sorted position outside its list")),
    }
}

/// The terms of `items`, sorted and without repetitions, charging one unit
/// per item and the comparison of each item with the last one kept.
pub(super) fn unique_sorted(items: &[Term], context: &mut Context) -> Result<Vec<Term>> {
    let positions = sorted_order(items, context)?;
    let mut unique: Vec<Term> = Vec::new();
    let mut index = 0;
    while index < positions.len() {
        context.charge(1)?;
        let item = item_at(items, &positions, index)?;
        if is_new(&unique, item, context)? {
            unique.push(item.clone());
        }
        index += 1;
    }
    Ok(unique)
}

/// Whether `item` differs from the last term of the sorted list `unique`.
fn is_new(unique: &[Term], item: &Term, context: &mut Context) -> Result<bool> {
    match unique.last() {
        Some(last) => Ok(order::compare(last, item, context)? != Ordering::Equal),
        None => Ok(true),
    }
}

/// Whether the sorted list `sorted` holds a term equal to `key`: a binary
/// search, charged by its comparisons.
pub(super) fn contains(sorted: &[Term], key: &Term, context: &mut Context) -> Result<bool> {
    let (_, found) = search(sorted, key, context)?;
    Ok(found)
}

/// The position of `key` in the sorted list of items `sorted`, and whether
/// an item with an equal term is there: a binary search, charged by its
/// comparisons. Without such an item, the position is where `key` belongs.
pub(super) fn search<T: SortItem>(
    sorted: &[T],
    key: &Term,
    context: &mut Context,
) -> Result<(usize, bool)> {
    let mut low = 0;
    let mut high = sorted.len();
    while low < high {
        let middle = low + (high - low) / 2;
        match order::compare(sorted[middle].sort_term(), key, context)? {
            Ordering::Less => low = middle + 1,
            Ordering::Greater => high = middle,
            Ordering::Equal => return Ok((middle, true)),
        }
    }
    Ok((low, false))
}
