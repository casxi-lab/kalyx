//! The tokens of the input syntax.
//!
//! The lexer reads one token at a time, when the parser asks for it, so its
//! errors come in reading order. Whitespace (space, tab, line feed, form feed
//! and carriage return) separates tokens and is otherwise skipped. A token is
//! one of the operators `+ - * / ^`, a parenthesis, an identifier, a number
//! literal or the end of the input:
//!
//! - an identifier follows the rule of symbol names of the term core: an
//!   ASCII letter or `_`, then ASCII letters, digits and `_`;
//! - a number literal starts with a digit or a point and runs over every
//!   ASCII letter, digit, `_` and point that follows, so the whole run is one
//!   token, which the parser converts with the decimal literal function of the
//!   exact numbers. Only the forms `1` and `1.5` are valid in this release,
//!   and every other run, such as `.5`, `1.`, `1e3` or `2x`, is a syntax error
//!   inside one literal, never two operands.
//!
//! Every other character starts no token and is a syntax error with the span
//! of the whole character. Each token charges one work unit per byte that it
//! reads, its leading whitespace included, and the end of the input one unit
//! more, after the token is scanned and before it is returned.

use crate::term::{character_length, continues_name, is_digit, starts_name};
use crate::{Context, Error, FaultKind, Result};

use super::tree::SyntaxRange;

/// The kind of a token.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SyntaxTokenKind {
    /// A number literal: a run that starts with a digit or a point.
    Number,
    /// An identifier.
    Identifier,
    /// `+`.
    Plus,
    /// `-`.
    Minus,
    /// `*`.
    Star,
    /// `/`.
    Slash,
    /// `^`.
    Caret,
    /// `(`.
    Open,
    /// `)`.
    Close,
    /// The end of the input, with an empty range at its end.
    End,
}

/// A token: its kind and its range in the source.
#[derive(Clone, Copy, Debug)]
pub(super) struct SyntaxToken {
    pub(super) kind: SyntaxTokenKind,
    pub(super) range: SyntaxRange,
}

/// Reads the token that follows byte `*position` of `source`, after the
/// whitespace before it, and moves `*position` to the end of the token.
///
/// Scans the token, then charges one unit per byte from `*position` to the
/// end of the token, and one more at the end of the input.
///
/// # Errors
///
/// `Fault(Syntax)` for a character that starts no token, with the span of
/// the character; the request failures of the charge, with the span of the
/// token.
pub(super) fn next_token(
    source: &str,
    position: &mut usize,
    context: &mut Context,
) -> Result<SyntaxToken> {
    let bytes = source.as_bytes();
    let start = skip_whitespace(bytes, *position);
    let token = token_at(bytes, start)?;
    let read = token.range.end.saturating_sub(*position) as u64;
    let charge = if is_end(token.kind) {
        read.saturating_add(1)
    } else {
        read
    };
    context.charge_at(charge, token.range.span())?;
    *position = token.range.end;
    Ok(token)
}

/// Whether `kind` is the end of the input.
const fn is_end(kind: SyntaxTokenKind) -> bool {
    matches!(kind, SyntaxTokenKind::End)
}

/// The position of the first byte at or after `start` that is not
/// whitespace, or the end of `bytes`.
fn skip_whitespace(bytes: &[u8], start: usize) -> usize {
    let mut index = start;
    while index < bytes.len() && is_whitespace(bytes[index]) {
        index += 1;
    }
    index
}

/// The token that starts at byte `start`, which is not whitespace and starts
/// a character.
fn token_at(bytes: &[u8], start: usize) -> Result<SyntaxToken> {
    let byte = match bytes.get(start) {
        Some(byte) => *byte,
        None => return Ok(token(SyntaxTokenKind::End, start, start)),
    };
    match byte {
        b'+' => Ok(single(SyntaxTokenKind::Plus, start)),
        b'-' => Ok(single(SyntaxTokenKind::Minus, start)),
        b'*' => Ok(single(SyntaxTokenKind::Star, start)),
        b'/' => Ok(single(SyntaxTokenKind::Slash, start)),
        b'^' => Ok(single(SyntaxTokenKind::Caret, start)),
        b'(' => Ok(single(SyntaxTokenKind::Open, start)),
        b')' => Ok(single(SyntaxTokenKind::Close, start)),
        _ => run_at(bytes, start, byte),
    }
}

/// The literal or identifier that starts with `byte` at `start`.
fn run_at(bytes: &[u8], start: usize, byte: u8) -> Result<SyntaxToken> {
    if is_digit(byte) || byte == b'.' {
        Ok(token(
            SyntaxTokenKind::Number,
            start,
            literal_end(bytes, start),
        ))
    } else if starts_name(byte) {
        Ok(token(
            SyntaxTokenKind::Identifier,
            start,
            name_end(bytes, start),
        ))
    } else {
        // Every byte before `start` that the lexer passed is ASCII, so
        // `start` starts a character, and `byte` gives its length.
        let range = SyntaxRange::new(start, start.saturating_add(character_length(byte)));
        Err(Error::new(
            FaultKind::Syntax,
            range.span(),
            "a character that is not part of the input syntax",
        ))
    }
}

/// The end of the run of a number literal that starts at `start`: every
/// ASCII letter, digit, `_` and point that follows.
fn literal_end(bytes: &[u8], start: usize) -> usize {
    let mut index = start;
    while index < bytes.len() && continues_literal(bytes[index]) {
        index += 1;
    }
    index
}

/// The end of the identifier that starts at `start`.
fn name_end(bytes: &[u8], start: usize) -> usize {
    let mut index = start;
    while index < bytes.len() && continues_name(bytes[index]) {
        index += 1;
    }
    index
}

/// Whether `byte` continues the run of a number literal: an ASCII letter,
/// digit, `_` or point.
const fn continues_literal(byte: u8) -> bool {
    continues_name(byte) || byte == b'.'
}

/// Whether `byte` is whitespace: space, tab, line feed, form feed or
/// carriage return.
const fn is_whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\x0C' | b'\r')
}

/// The token of `kind` over the bytes from `start` up to `end`.
const fn token(kind: SyntaxTokenKind, start: usize, end: usize) -> SyntaxToken {
    SyntaxToken {
        kind,
        range: SyntaxRange::new(start, end),
    }
}

/// The token of `kind` over the one byte at `start`.
const fn single(kind: SyntaxTokenKind, start: usize) -> SyntaxToken {
    token(kind, start, start + 1)
}
