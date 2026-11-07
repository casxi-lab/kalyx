//! Property tests of the canonical forms of terms.
//!
//! Each of the six canonical-form invariants of
//! `docs/components/terms/contract.md` has a property test of 1,000 cases
//! from a fixed seed, and the negative-exponent invariant has a second one,
//! as the testing obligations of that contract ask: uniqueness, idempotence,
//! the order of terms in sums and products, the merging of like terms and
//! coefficients, the elimination of 0 and 1, integer powers, and
//! $N(\mathrm{input}) \subseteq N(\mathrm{output})$ for every constructor.
//!
//! The inputs come from a generator written here: random expression trees
//! over the symbols `x`, `y` and `z`, small rationals with 0, 1 and $-1$
//! among them, and integer exponents with 0, 1, $-1$ and other negative ones,
//! built through the public constructors of `kalyx::term` alone. The
//! generator writes on purpose like terms; the shapes $x^2 \cdot x^{-1}$,
//! $x \cdot x^{-1}$, $0 \cdot x^{-1}$ and $(x^{-1})^0$; several scaled copies
//! of one sum $s$ among the operands of a sum, $[2s, -s, -s]$,
//! $[2s, -s, 2s, -s]$ and copies with random scales; sums scaled by random
//! rationals and scaled copies of nested sums; and sums whose content is not
//! 1 as factors and as bases, such as $(2x + 2y) z$ and $(1 - x)^{-1}$. The
//! checks read terms through the accessors only, with a structural equality,
//! the total order, the content and the primitive part of a sum, and the set
//! $N(t)$, whose sums are compared by their primitive parts, all written here
//! from the contract, and an independent model evaluates both the expression
//! tree and the canonical term exactly, with integers of any size written
//! here, at random rational points: where the input is defined the two values
//! are equal, and where it is undefined the term is undefined too. Counters
//! name what the cases exercised, and each property asserts that its cases
//! exercised every shape that it depends on.
//!
//! Each case of a property draws from its own seed, the next output of a
//! SplitMix64 started at the fixed seed of the property. A failing case
//! prints its index, its seed and its inputs, and
//! `check(&mut Case::new(property, index, seed), &mut Tally::default())`,
//! with the case function of the property as `check`, runs it alone.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "a failed check panics, and the guard of its case prints the seed and the inputs"
)]

use std::cmp::Ordering;

use kalyx::context::CancelFlag;
use kalyx::number::{Integer, Rational};
use kalyx::term::{Term, TermKind};
use kalyx::{Context, Error, ErrorKind, FaultKind, Limits};

/// The cases of each property.
const CASES: u64 = 1_000;

/// The draws of one case; an input that fails with a division by zero is
/// checked and drawn again.
const ATTEMPTS: usize = 100;

/// The sample points of the model in each case.
const POINTS: usize = 4;

/// The random orders and groupings of each input in the uniqueness property,
/// besides the plain construction.
const REGROUPINGS: usize = 3;

/// The levels of operations of a generated input.
const DEPTH: u32 = 6;

const UNIQUENESS_SEED: u64 = 0x5EED_0000_0000_0001;
const IDEMPOTENCE_SEED: u64 = 0x5EED_0000_0000_0002;
const ORDER_SEED: u64 = 0x5EED_0000_0000_0003;
const MERGING_SEED: u64 = 0x5EED_0000_0000_0004;
const ELIMINATION_SEED: u64 = 0x5EED_0000_0000_0005;
const POWERS_SEED: u64 = 0x5EED_0000_0000_0006;
const NEGATIVE_BASES_SEED: u64 = 0x5EED_0000_0000_0007;

/// The symbols of the generated terms.
const NAMES: [&str; 3] = ["x", "y", "z"];

/// The names that are not symbols.
const RESERVED: [&str; 3] = ["pi", "i", "undefined"];

/// The numbers of the generated terms, as a numerator and a positive
/// denominator; 0, 1 and $-1$ are drawn most often.
const NUMBERS: [(i64, i64); 14] = [
    (0, 1),
    (0, 1),
    (1, 1),
    (1, 1),
    (-1, 1),
    (-1, 1),
    (2, 1),
    (-2, 1),
    (3, 1),
    (1, 2),
    (-1, 3),
    (3, 2),
    (-5, 4),
    (2, 3),
];

/// The exponents of the generated powers; 0, 1 and $-1$ are drawn most often.
const EXPONENTS: [i64; 12] = [-3, -2, -1, -1, -1, 0, 0, 1, 1, 2, 2, 3];

/// The exponents to which the power property raises its bases.
const POWER_EXPONENTS: [i64; 13] = [-4, -3, -2, -1, -1, 0, 0, 1, 1, 2, 2, 3, 4];

/// Pairs of scalars that add up to 1, neither of them 0 or 1, for the scaled
/// copies of nested sums.
const PAIRS_OF_ONE: [((i64, i64), (i64, i64)); 5] = [
    ((2, 1), (-1, 1)),
    ((-1, 1), (2, 1)),
    ((3, 1), (-2, 1)),
    ((1, 2), (1, 2)),
    ((-2, 1), (3, 1)),
];

/// The nonzero exponents of the like factors of the merging property.
const NONZERO_EXPONENTS: [i64; 6] = [-3, -2, -1, 1, 2, 3];

/// The scalars of the like monomials of the merging property: neither 0 nor
/// 1, so that each scaled term is a monomial of its own.
const SCALES: [(i64, i64); 8] = [
    (2, 1),
    (-1, 1),
    (3, 1),
    (1, 2),
    (-2, 3),
    (5, 1),
    (-3, 1),
    (3, 4),
];

/// The constants of the differences $c - x$ of the generator, whose content
/// is $-1$.
const MINUENDS: [(i64, i64); 5] = [(1, 1), (1, 1), (2, 1), (-1, 1), (1, 2)];

/// The counters of the scaled sums that reach the constructors, as
/// [`count_scaled_sums`], [`count_negated_sum`] and [`count_scaled_base`]
/// name them: several scaled copies of one sum $s$ among the operands of a
/// sum, in the patterns $[2s, -s, -s]$ and $[2s, -s, 2s, -s]$ and with other
/// scales; a sum times numbers alone, or negated; a sum whose content is not
/// 1 among other factors of a product; and a power of such a sum. Every
/// property asserts that its cases exercised each of them.
const SCALED_SUMS: [&str; 6] = [
    "operands [2s, -s, -s] of a sum",
    "operands [2s, -s, 2s, -s] of a sum",
    "other scaled copies of one sum among the operands of a sum",
    "sums scaled by a number",
    "sums whose content is not 1 among the factors of a product",
    "powers of sums whose content is not 1",
];

/// The values of the symbols at the sample points: 0, drawn twice as often as
/// any other value, 1 and $-1$, at which inputs are often undefined, and other
/// small nonzero rationals, at which they mostly are defined.
const VALUES: [(i64, i64); 17] = [
    (0, 1),
    (0, 1),
    (1, 1),
    (-1, 1),
    (2, 1),
    (-2, 1),
    (1, 2),
    (-1, 2),
    (3, 1),
    (-3, 1),
    (2, 3),
    (-3, 2),
    (5, 2),
    (1, 3),
    (-4, 3),
    (7, 5),
    (-5, 7),
];

// ---------------------------------------------------------------------------
// The random source and the cases

/// SplitMix64, a fixed-seed generator written here; the tests use no
/// external generator.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..bound`.
    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    /// An index into a list of `len` items; the lists are short, so the
    /// conversions lose nothing.
    fn index(&mut self, len: usize) -> usize {
        self.below(len as u64) as usize
    }

    /// True with the probability `numerator / denominator`.
    fn chance(&mut self, numerator: u64, denominator: u64) -> bool {
        self.below(denominator) < numerator
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.index(items.len())]
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for last in (1..items.len()).rev() {
            let other = self.index(last + 1);
            items.swap(last, other);
        }
    }
}

/// One case of a property: its seed, its random source, its context and the
/// inputs it drew. A case that panics prints its seed and its inputs when it
/// is dropped.
struct Case {
    property: &'static str,
    index: u64,
    seed: u64,
    random: SplitMix64,
    context: Context,
    inputs: Vec<String>,
}

impl Case {
    fn new(property: &'static str, index: u64, seed: u64) -> Self {
        Self {
            property,
            index,
            seed,
            random: SplitMix64(seed),
            context: context(),
            inputs: Vec::new(),
        }
    }

    /// Records an input for the report of a failure.
    fn note(&mut self, input: &Expression) {
        self.inputs.push(input.text());
    }

    /// Marks the last input as one that failed with a division by zero, was
    /// found undefined at every sample point and was drawn again.
    fn drawn_again(&mut self, tally: &mut Tally) {
        if let Some(last) = self.inputs.last_mut() {
            last.push_str(" (a division by zero; drawn again)");
        }
        tally.add("inputs drawn again after a division by zero", 1);
    }
}

impl Drop for Case {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "{}: case {} of {CASES} failed; its seed is {:#018x}",
                self.property, self.index, self.seed
            );
            for input in &self.inputs {
                eprintln!("  input: {input}");
            }
        }
    }
}

/// Counts of what the cases of a property exercised, printed after the run.
#[derive(Default)]
struct Tally(Vec<(&'static str, u64)>);

impl Tally {
    fn add(&mut self, name: &'static str, amount: u64) {
        match self.0.iter_mut().find(|entry| entry.0 == name) {
            Some(entry) => entry.1 += amount,
            None => self.0.push((name, amount)),
        }
    }

    fn get(&self, name: &str) -> u64 {
        self.0
            .iter()
            .find(|entry| entry.0 == name)
            .map_or(0, |entry| entry.1)
    }

    /// Asserts that the cases exercised each of `names`.
    fn require(&self, property: &str, names: &[&str]) {
        for name in names {
            assert!(self.get(name) > 0, "{property}: no case exercised {name}");
        }
    }

    fn summary(&self) -> String {
        let parts: Vec<String> = self
            .0
            .iter()
            .map(|(name, count)| format!("{name}: {count}"))
            .collect();
        parts.join("; ")
    }
}

/// Runs the cases of a property, each from its own seed: the next output of a
/// SplitMix64 started at `seed`.
fn run(property: &'static str, seed: u64, check: fn(&mut Case, &mut Tally)) -> Tally {
    let mut seeds = SplitMix64(seed);
    let mut tally = Tally::default();
    for index in 0..CASES {
        let mut case = Case::new(property, index, seeds.next());
        check(&mut case, &mut tally);
        tally.add("cases", 1);
    }
    assert_eq!(tally.get("cases"), CASES);
    println!("{property}: {}", tally.summary());
    tally
}

/// A context whose limits are far above every case: the properties concern
/// the canonical forms, not the limits, and no amount of work is asserted.
fn context() -> Context {
    Context::new(
        Limits::new()
            .with_max_work(u64::MAX)
            .with_max_output_bytes(u64::MAX)
            .with_max_depth(1 << 12)
            .with_max_nodes(1 << 32)
            .with_max_storage_bytes(1 << 40)
            .with_max_integer_bits(1 << 16)
            .with_max_exponent(1 << 16),
        CancelFlag::new(),
    )
}

// ---------------------------------------------------------------------------
// Exact arithmetic of the model

/// An integer of any size for the model: a sign and a magnitude in limbs of
/// 32 bits, the least significant first, with no zero limb at the top. Zero
/// has no limbs and is not negative.
#[derive(Clone, Debug)]
struct Big {
    negative: bool,
    limbs: Vec<u32>,
}

/// $10^9$, the base of the decimal text of a [`Big`].
const BILLION: u64 = 1_000_000_000;

impl Big {
    fn new(negative: bool, mut limbs: Vec<u32>) -> Self {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        let negative = negative && !limbs.is_empty();
        Self { negative, limbs }
    }

    fn from_i64(value: i64) -> Self {
        let mut magnitude = value.unsigned_abs();
        let mut limbs = Vec::new();
        while magnitude != 0 {
            limbs.push(low_limb(magnitude));
            magnitude >>= 32;
        }
        Self::new(value < 0, limbs)
    }

    /// The integer of a decimal text with an optional leading `-`.
    fn parse(text: &str) -> Self {
        let (negative, digits) = match text.strip_prefix('-') {
            Some(digits) => (true, digits),
            None => (false, text),
        };
        let mut limbs: Vec<u32> = Vec::new();
        for digit in digits.bytes() {
            assert!(digit.is_ascii_digit(), "not a decimal integer: {text}");
            let mut carry = u64::from(digit - b'0');
            for limb in &mut limbs {
                let value = u64::from(*limb) * 10 + carry;
                *limb = low_limb(value);
                carry = value >> 32;
            }
            if carry != 0 {
                limbs.push(low_limb(carry));
            }
        }
        Self::new(negative, limbs)
    }

    fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    fn negated(&self) -> Self {
        Self::new(!self.negative, self.limbs.clone())
    }

    fn magnitude(&self) -> Self {
        Self::new(false, self.limbs.clone())
    }

    fn plus(&self, other: &Self) -> Self {
        if self.negative == other.negative {
            return Self::new(self.negative, add_magnitudes(&self.limbs, &other.limbs));
        }
        match compare_magnitudes(&self.limbs, &other.limbs) {
            Ordering::Less => Self::new(
                other.negative,
                subtract_magnitudes(&other.limbs, &self.limbs),
            ),
            Ordering::Equal => Self::new(false, Vec::new()),
            Ordering::Greater => Self::new(
                self.negative,
                subtract_magnitudes(&self.limbs, &other.limbs),
            ),
        }
    }

    fn times(&self, other: &Self) -> Self {
        Self::new(
            self.negative != other.negative,
            multiply_magnitudes(&self.limbs, &other.limbs),
        )
    }

    fn order(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => compare_magnitudes(&self.limbs, &other.limbs),
            (true, true) => compare_magnitudes(&other.limbs, &self.limbs),
        }
    }

    /// The decimal text, with a leading `-` when negative.
    fn decimal(&self) -> String {
        let mut limbs = self.limbs.clone();
        // Digits in base $10^9$, the least significant first.
        let mut chunks = Vec::new();
        while !limbs.is_empty() {
            let mut remainder = 0_u64;
            for limb in limbs.iter_mut().rev() {
                let value = (remainder << 32) | u64::from(*limb);
                *limb = low_limb(value / BILLION);
                remainder = value % BILLION;
            }
            while limbs.last() == Some(&0) {
                limbs.pop();
            }
            chunks.push(remainder);
        }
        let mut text = String::from(if self.negative { "-" } else { "" });
        match chunks.pop() {
            Some(first) => text.push_str(&first.to_string()),
            None => text.push('0'),
        }
        while let Some(chunk) = chunks.pop() {
            let digits = chunk.to_string();
            for _ in digits.len()..9 {
                text.push('0');
            }
            text.push_str(&digits);
        }
        text
    }
}

/// The low 32 bits of `value`.
fn low_limb(value: u64) -> u32 {
    (value & 0xFFFF_FFFF) as u32
}

fn compare_magnitudes(left: &[u32], right: &[u32]) -> Ordering {
    left.len()
        .cmp(&right.len())
        .then_with(|| left.iter().rev().cmp(right.iter().rev()))
}

fn add_magnitudes(left: &[u32], right: &[u32]) -> Vec<u32> {
    let (long, short) = if left.len() >= right.len() {
        (left, right)
    } else {
        (right, left)
    };
    let mut sum = Vec::with_capacity(long.len() + 1);
    let mut carry = 0_u64;
    for (index, limb) in long.iter().enumerate() {
        let other = u64::from(short.get(index).copied().unwrap_or(0));
        let value = u64::from(*limb) + other + carry;
        sum.push(low_limb(value));
        carry = value >> 32;
    }
    if carry != 0 {
        sum.push(low_limb(carry));
    }
    sum
}

/// `left - right`, for `left` at least `right`.
fn subtract_magnitudes(left: &[u32], right: &[u32]) -> Vec<u32> {
    let mut difference = Vec::with_capacity(left.len());
    let mut borrow = 0_u64;
    for (index, limb) in left.iter().enumerate() {
        let subtrahend = u64::from(right.get(index).copied().unwrap_or(0)) + borrow;
        let minuend = u64::from(*limb);
        if minuend >= subtrahend {
            difference.push(low_limb(minuend - subtrahend));
            borrow = 0;
        } else {
            difference.push(low_limb(minuend + (1 << 32) - subtrahend));
            borrow = 1;
        }
    }
    difference
}

fn multiply_magnitudes(left: &[u32], right: &[u32]) -> Vec<u32> {
    let mut product = vec![0_u32; left.len() + right.len()];
    for (i, a) in left.iter().enumerate() {
        let mut carry = 0_u64;
        for (j, b) in right.iter().enumerate() {
            let value = u64::from(*a) * u64::from(*b) + u64::from(product[i + j]) + carry;
            product[i + j] = low_limb(value);
            carry = value >> 32;
        }
        product[i + right.len()] = low_limb(carry);
    }
    product
}

/// An exact rational of the model: a numerator over a positive denominator,
/// not reduced, so that two fractions are equal when their cross products
/// are.
#[derive(Clone, Debug)]
struct Fraction {
    numerator: Big,
    denominator: Big,
}

impl Fraction {
    fn new(numerator: i64, denominator: i64) -> Self {
        assert!(
            denominator > 0,
            "the denominators of the tables are positive"
        );
        Self {
            numerator: Big::from_i64(numerator),
            denominator: Big::from_i64(denominator),
        }
    }

    /// The value of a rational of the library, read through its decimal
    /// parts.
    fn of(value: &Rational) -> Self {
        Self {
            numerator: Big::parse(&value.numerator().to_string()),
            denominator: Big::parse(&value.denominator().to_string()),
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    fn is_one(&self) -> bool {
        self.equals(&Self::new(1, 1))
    }

    fn plus(&self, other: &Self) -> Self {
        Self {
            numerator: self
                .numerator
                .times(&other.denominator)
                .plus(&other.numerator.times(&self.denominator)),
            denominator: self.denominator.times(&other.denominator),
        }
    }

    fn times(&self, other: &Self) -> Self {
        Self {
            numerator: self.numerator.times(&other.numerator),
            denominator: self.denominator.times(&other.denominator),
        }
    }

    fn negated(&self) -> Self {
        Self {
            numerator: self.numerator.negated(),
            denominator: self.denominator.clone(),
        }
    }

    /// The inverse, or `None` for zero, whose inverse is undefined.
    fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let numerator = if self.numerator.negative {
            self.denominator.negated()
        } else {
            self.denominator.clone()
        };
        Some(Self {
            numerator,
            denominator: self.numerator.magnitude(),
        })
    }

    /// The power to an integer exponent, with $0^0 = 1$, or `None` for a
    /// negative power of zero.
    fn power(&self, exponent: i64) -> Option<Self> {
        let mut base = if exponent < 0 {
            self.inverse()?
        } else {
            self.clone()
        };
        let mut remaining = exponent.unsigned_abs();
        let mut result = Self::new(1, 1);
        while remaining != 0 {
            if remaining & 1 == 1 {
                result = result.times(&base);
            }
            remaining >>= 1;
            if remaining != 0 {
                base = base.times(&base);
            }
        }
        Some(result)
    }

    fn order(&self, other: &Self) -> Ordering {
        self.numerator
            .times(&other.denominator)
            .order(&other.numerator.times(&self.denominator))
    }

    fn equals(&self, other: &Self) -> bool {
        self.order(other) == Ordering::Equal
    }

    fn text(&self) -> String {
        format!(
            "{}/{}",
            self.numerator.decimal(),
            self.denominator.decimal()
        )
    }
}

// ---------------------------------------------------------------------------
// The generator

/// An input of the generator: an expression tree that the public
/// constructors build bottom-up.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Expression {
    /// A number: a numerator and a positive denominator.
    Number(i64, i64),
    /// The symbol `NAMES[index]`.
    Symbol(usize),
    /// `Term::sum` of the operands.
    Sum(Vec<Expression>),
    /// `Term::product` of the operands.
    Product(Vec<Expression>),
    /// `power` of the base to the exponent.
    Power(Box<Expression>, i64),
    /// `negate` of the operand.
    Negation(Box<Expression>),
    /// `subtract` of the right operand from the left one.
    Difference(Box<Expression>, Box<Expression>),
    /// `divide` of the left operand by the right one.
    Quotient(Box<Expression>, Box<Expression>),
}

impl Expression {
    /// The text of the input, written as the calls that build it.
    fn text(&self) -> String {
        match self {
            Self::Number(numerator, 1) => numerator.to_string(),
            Self::Number(numerator, denominator) => format!("{numerator}/{denominator}"),
            Self::Symbol(index) => NAMES[*index].to_string(),
            Self::Sum(parts) => format!("sum({})", texts(parts)),
            Self::Product(parts) => format!("product({})", texts(parts)),
            Self::Power(base, exponent) => format!("power({}, {exponent})", base.text()),
            Self::Negation(operand) => format!("negate({})", operand.text()),
            Self::Difference(left, right) => {
                format!("subtract({}, {})", left.text(), right.text())
            }
            Self::Quotient(left, right) => format!("divide({}, {})", left.text(), right.text()),
        }
    }

    fn children(&self) -> Vec<&Self> {
        match self {
            Self::Number(..) | Self::Symbol(_) => Vec::new(),
            Self::Sum(parts) | Self::Product(parts) => parts.iter().collect(),
            Self::Power(operand, _) | Self::Negation(operand) => vec![operand.as_ref()],
            Self::Difference(left, right) | Self::Quotient(left, right) => {
                vec![left.as_ref(), right.as_ref()]
            }
        }
    }
}

fn texts(parts: &[Expression]) -> String {
    let list: Vec<String> = parts.iter().map(Expression::text).collect();
    list.join(", ")
}

/// The four shapes of the negative-exponent invariant, which the generator
/// writes on purpose: $b^2 \cdot b^{-1}$, $b \cdot b^{-1}$, $0 \cdot b^{-1}$
/// and $(b^{-1})^0$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    SquareTimesInverse,
    BaseTimesInverse,
    ZeroTimesInverse,
    InverseToTheZero,
}

const SHAPES: [Shape; 4] = [
    Shape::SquareTimesInverse,
    Shape::BaseTimesInverse,
    Shape::ZeroTimesInverse,
    Shape::InverseToTheZero,
];

impl Shape {
    fn name(self) -> &'static str {
        match self {
            Self::SquareTimesInverse => "shape x^2*x^-1",
            Self::BaseTimesInverse => "shape x*x^-1",
            Self::ZeroTimesInverse => "shape 0*x^-1",
            Self::InverseToTheZero => "shape (x^-1)^0",
        }
    }

    /// The expression of the shape on `base`, with the two factors of a
    /// product in a random order.
    fn on(self, base: Expression, random: &mut SplitMix64) -> Expression {
        let inverse = Expression::Power(Box::new(base.clone()), -1);
        let pair = |first: Expression, second: Expression, random: &mut SplitMix64| {
            if random.chance(1, 2) {
                Expression::Product(vec![first, second])
            } else {
                Expression::Product(vec![second, first])
            }
        };
        match self {
            Self::SquareTimesInverse => pair(Expression::Power(Box::new(base), 2), inverse, random),
            Self::BaseTimesInverse => pair(base, inverse, random),
            Self::ZeroTimesInverse => pair(Expression::Number(0, 1), inverse, random),
            Self::InverseToTheZero => Expression::Power(Box::new(inverse), 0),
        }
    }

    /// The shape of `expression` at its root, if it has one.
    fn of(expression: &Expression) -> Option<Self> {
        match expression {
            Expression::Product(operands) if operands.len() == 2 => {
                Self::of_pair(&operands[0], &operands[1])
                    .or_else(|| Self::of_pair(&operands[1], &operands[0]))
            }
            Expression::Power(inner, 0) if matches!(inner.as_ref(), Expression::Power(_, -1)) => {
                Some(Self::InverseToTheZero)
            }
            _ => None,
        }
    }

    /// The shape of the product of `factor` and `inverse`.
    fn of_pair(factor: &Expression, inverse: &Expression) -> Option<Self> {
        let Expression::Power(base, -1) = inverse else {
            return None;
        };
        match factor {
            Expression::Number(0, 1) => Some(Self::ZeroTimesInverse),
            Expression::Power(square, 2) if square == base => Some(Self::SquareTimesInverse),
            _ if factor == base.as_ref() => Some(Self::BaseTimesInverse),
            _ => None,
        }
    }
}

/// Counts the shapes that occur anywhere in `expression`.
fn count_shapes(expression: &Expression, tally: &mut Tally) {
    if let Some(shape) = Shape::of(expression) {
        tally.add(shape.name(), 1);
    }
    for child in expression.children() {
        count_shapes(child, tally);
    }
}

/// Collects the bases of the negative powers and the divisors of the
/// quotients of `expression`, as written in the generator tree.
fn written_negative_bases<'a>(expression: &'a Expression, bases: &mut Vec<&'a Expression>) {
    match expression {
        Expression::Power(base, exponent) if *exponent < 0 => bases.push(base),
        Expression::Quotient(_, divisor) => bases.push(divisor),
        _ => {}
    }
    for child in expression.children() {
        written_negative_bases(child, bases);
    }
}

/// A random input: an operation at the root, with at most [`DEPTH`] levels
/// of operations.
fn input(random: &mut SplitMix64) -> Expression {
    operation(random, DEPTH)
}

/// A random expression of at most `depth` levels of operations, which ends
/// early in a leaf at one level in six.
fn expression(random: &mut SplitMix64, depth: u32) -> Expression {
    if depth == 0 || random.chance(1, 6) {
        return leaf(random);
    }
    operation(random, depth)
}

/// A random operation of at most `depth` levels, at least one.
fn operation(random: &mut SplitMix64, depth: u32) -> Expression {
    let below = depth - 1;
    match random.below(21) {
        0..=2 => Expression::Sum(operands(random, below)),
        3..=5 => Expression::Product(operands(random, below)),
        6..=8 => {
            let base = expression(random, below);
            Expression::Power(Box::new(base), random.pick(&EXPONENTS))
        }
        9 => Expression::Negation(Box::new(expression(random, below))),
        10 => {
            let left = expression(random, below);
            Expression::Difference(Box::new(left), Box::new(expression(random, below)))
        }
        11 => {
            let left = expression(random, below);
            Expression::Quotient(Box::new(left), Box::new(expression(random, below)))
        }
        12 | 13 => like_terms(random, below),
        14 | 15 => {
            let shape = random.pick(&SHAPES);
            let base = shape_base(random, below);
            shape.on(base, random)
        }
        16 => nested_scaled_sums(random, below.min(2)),
        17 | 18 => scaled_copies(random, below.min(2)),
        19 => scaled_factor(random, below),
        _ => scaled_base(random, below),
    }
}

/// A symbol or a number.
fn leaf(random: &mut SplitMix64) -> Expression {
    if random.chance(7, 10) {
        Expression::Symbol(random.index(NAMES.len()))
    } else {
        let (numerator, denominator) = random.pick(&NUMBERS);
        Expression::Number(numerator, denominator)
    }
}

/// The operands of a sum or a product: none to four.
fn operands(random: &mut SplitMix64, depth: u32) -> Vec<Expression> {
    let count = random.pick(&[0, 1, 2, 2, 3, 3, 4, 4]);
    let mut list = Vec::with_capacity(count);
    for _ in 0..count {
        list.push(expression(random, depth));
    }
    list
}

/// An expression in which one operand occurs twice, built apart, so that
/// like monomials and like factors meet.
fn like_terms(random: &mut SplitMix64, depth: u32) -> Expression {
    let operand = expression(random, depth);
    let copy = operand.clone();
    let (p, q) = random.pick(&NUMBERS);
    let (r, s) = random.pick(&NUMBERS);
    match random.below(7) {
        0 => Expression::Sum(vec![operand, copy]),
        1 => Expression::Sum(vec![
            operand,
            Expression::Product(vec![Expression::Number(p, q), copy]),
        ]),
        2 => Expression::Sum(vec![operand, Expression::Negation(Box::new(copy))]),
        3 => Expression::Difference(Box::new(operand), Box::new(copy)),
        4 => Expression::Product(vec![operand, copy]),
        5 => Expression::Product(vec![
            operand,
            Expression::Power(Box::new(copy), random.pick(&EXPONENTS)),
        ]),
        _ => Expression::Sum(vec![
            Expression::Product(vec![Expression::Number(p, q), operand]),
            Expression::Product(vec![copy, Expression::Number(r, s)]),
        ]),
    }
}

/// Scaled copies of nested sums. With $T_0$ a random sum and
/// $T_i = u_i + d_i T_{i-1}$ for symbols $u_i$, it is
/// $a T_n + b T_n + \sum_{i=1}^{n} e_i T_{i-1}$ with $a + b = 1$ and
/// $d_i + e_i = 1$. A number distributes over a sum, so $d_i T_{i-1}$ is
/// scaled into the monomials of $T_i$; the copies $a T_n$ and $b T_n$ add up
/// to $T_n$, whose monomials from $d_n T_{n-1}$ add up with those of
/// $e_n T_{n-1}$ to $T_{n-1}$, and so on down to $T_0$: the sum is
/// $u_n + \dots + u_1 + T_0$ in every grouping.
fn nested_scaled_sums(random: &mut SplitMix64, depth: u32) -> Expression {
    let levels = 1 + random.index(3);
    let mut parts = Vec::with_capacity(levels + 2);
    let symbol = Expression::Symbol(random.index(NAMES.len()));
    let mut inner = Expression::Sum(vec![symbol, expression(random, depth)]);
    for _ in 0..levels {
        let ((d, d_denominator), (e, e_denominator)) = random.pick(&PAIRS_OF_ONE);
        parts.push(Expression::Product(vec![
            Expression::Number(e, e_denominator),
            inner.clone(),
        ]));
        let symbol = Expression::Symbol(random.index(NAMES.len()));
        let scaled = Expression::Product(vec![Expression::Number(d, d_denominator), inner]);
        inner = Expression::Sum(vec![symbol, scaled]);
    }
    let ((a, a_denominator), (b, b_denominator)) = random.pick(&PAIRS_OF_ONE);
    parts.push(Expression::Product(vec![
        Expression::Number(a, a_denominator),
        inner.clone(),
    ]));
    parts.push(Expression::Product(vec![
        Expression::Number(b, b_denominator),
        inner,
    ]));
    random.shuffle(&mut parts);
    Expression::Sum(parts)
}

/// Several scaled copies of one sum $s$, each written and built apart, as
/// the operands of a sum in a random order: $[2s, -s, -s]$,
/// $[2s, -s, 2s, -s]$, or two to four copies with random scales, 0, 1 and
/// $-1$ among them; now and then with one more operand.
fn scaled_copies(random: &mut SplitMix64, depth: u32) -> Expression {
    let sum = copied_sum(random, depth);
    let scales = match random.below(3) {
        0 => vec![(2, 1), (-1, 1), (-1, 1)],
        1 => vec![(2, 1), (-1, 1), (2, 1), (-1, 1)],
        _ => {
            let count = 2 + random.index(3);
            let mut scales = Vec::with_capacity(count);
            for _ in 0..count {
                scales.push(random.pick(&NUMBERS));
            }
            scales
        }
    };
    let mut parts = Vec::with_capacity(scales.len() + 1);
    for scale in scales {
        parts.push(scaled(scale, sum.clone(), random));
    }
    if random.chance(1, 4) {
        parts.push(expression(random, depth));
    }
    random.shuffle(&mut parts);
    Expression::Sum(parts)
}

/// `scale` times `sum`, written as the sum itself for 1 and as its negation
/// for $-1$ half of the time, and otherwise as the product with the number
/// on either side.
fn scaled(scale: (i64, i64), sum: Expression, random: &mut SplitMix64) -> Expression {
    if scale == (1, 1) && random.chance(1, 2) {
        return sum;
    }
    if scale == (-1, 1) && random.chance(1, 2) {
        return Expression::Negation(Box::new(sum));
    }
    let number = Expression::Number(scale.0, scale.1);
    if random.chance(1, 2) {
        Expression::Product(vec![number, sum])
    } else {
        Expression::Product(vec![sum, number])
    }
}

/// The sum of which [`scaled_copies`] writes copies: two symbols, $x + y$; a
/// symbol and a reciprocal, with a constant half of the time, such as
/// $x + y^{-1}$, whose copies cancel to a witness; a symbol and a random
/// expression; or a sum whose content is mostly not 1, from [`content_sum`].
fn copied_sum(random: &mut SplitMix64, depth: u32) -> Expression {
    let first = random.index(NAMES.len());
    let second = (first + 1 + random.index(NAMES.len() - 1)) % NAMES.len();
    match random.below(4) {
        0 => Expression::Sum(vec![Expression::Symbol(first), Expression::Symbol(second)]),
        1 => {
            let symbol = Expression::Symbol(random.index(NAMES.len()));
            let mut parts = vec![
                Expression::Symbol(first),
                Expression::Power(Box::new(symbol), -1),
            ];
            if random.chance(1, 2) {
                let (numerator, denominator) = random.pick(&NUMBERS);
                parts.push(Expression::Number(numerator, denominator));
            }
            random.shuffle(&mut parts);
            Expression::Sum(parts)
        }
        2 => Expression::Sum(vec![Expression::Symbol(first), expression(random, depth)]),
        _ => content_sum(random, depth),
    }
}

/// A sum whose content is mostly not 1, as a factor or a base takes it by
/// its primitive part: two or three symbols times scalars that are neither 0
/// nor 1, such as $2x + 2y$ or $3x + 2y$, with a constant half of the time; a
/// difference $c - x$, whose content is $-1$; a random sum times a scalar
/// that is neither 0 nor 1; or a constant $c$, neither 0 nor 1, with a
/// reciprocal that cancels, $c + 0 \cdot x^{-1}$, whose content is its
/// constant.
fn content_sum(random: &mut SplitMix64, depth: u32) -> Expression {
    let symbol = random.index(NAMES.len());
    match random.below(4) {
        0 => {
            let count = 2 + random.index(2);
            let mut parts = Vec::with_capacity(count + 1);
            for offset in 0..count {
                let (numerator, denominator) = random.pick(&SCALES);
                parts.push(Expression::Product(vec![
                    Expression::Number(numerator, denominator),
                    Expression::Symbol((symbol + offset) % NAMES.len()),
                ]));
            }
            if random.chance(1, 2) {
                let (numerator, denominator) = random.pick(&NUMBERS);
                parts.push(Expression::Number(numerator, denominator));
            }
            random.shuffle(&mut parts);
            Expression::Sum(parts)
        }
        1 => {
            let (numerator, denominator) = random.pick(&MINUENDS);
            Expression::Difference(
                Box::new(Expression::Number(numerator, denominator)),
                Box::new(Expression::Symbol(symbol)),
            )
        }
        2 => {
            let sum = Expression::Sum(vec![Expression::Symbol(symbol), expression(random, depth)]);
            let scale = random.pick(&SCALES);
            scaled(scale, sum, random)
        }
        _ => {
            let (numerator, denominator) = random.pick(&SCALES);
            let reciprocal = Expression::Power(Box::new(Expression::Symbol(symbol)), -1);
            Expression::Sum(vec![
                Expression::Number(numerator, denominator),
                reciprocal.clone(),
                Expression::Negation(Box::new(reciprocal)),
            ])
        }
    }
}

/// A product with a sum whose content is mostly not 1 among its two or three
/// operands, in a random order, such as $(2x + 2y) z$.
fn scaled_factor(random: &mut SplitMix64, depth: u32) -> Expression {
    let mut parts = vec![content_sum(random, depth.min(2)), expression(random, depth)];
    if random.chance(1, 3) {
        parts.push(expression(random, depth));
    }
    random.shuffle(&mut parts);
    Expression::Product(parts)
}

/// A power of a sum whose content is mostly not 1, such as $(1 - x)^{-1}$.
fn scaled_base(random: &mut SplitMix64, depth: u32) -> Expression {
    let base = content_sum(random, depth.min(2));
    Expression::Power(Box::new(base), random.pick(&EXPONENTS))
}

/// The base of a shape: mostly a symbol, now and then a sum whose content is
/// mostly not 1, from [`content_sum`], and otherwise any expression.
fn shape_base(random: &mut SplitMix64, depth: u32) -> Expression {
    match random.below(6) {
        0..=2 => Expression::Symbol(random.index(NAMES.len())),
        3 => content_sum(random, depth),
        _ => expression(random, depth),
    }
}

/// A base for the power property: often a power, a power of a power, a
/// product with a numeric operand, a number, a shape, a sum whose content is
/// mostly not 1, or a sum of which the generator writes scaled copies.
fn power_base(random: &mut SplitMix64) -> Expression {
    match random.below(12) {
        0..=2 => {
            let base = expression(random, DEPTH - 1);
            Expression::Power(Box::new(base), random.pick(&EXPONENTS))
        }
        3 => {
            let base = shape_base(random, 1);
            let inner = Expression::Power(Box::new(base), random.pick(&EXPONENTS));
            Expression::Power(Box::new(inner), random.pick(&EXPONENTS))
        }
        4 | 5 => {
            let (numerator, denominator) = random.pick(&NUMBERS);
            let first = expression(random, DEPTH - 1);
            let second = expression(random, DEPTH - 1);
            Expression::Product(vec![
                Expression::Number(numerator, denominator),
                first,
                second,
            ])
        }
        6 => {
            let (numerator, denominator) = random.pick(&NUMBERS);
            Expression::Number(numerator, denominator)
        }
        7 => {
            let shape = random.pick(&SHAPES);
            let base = shape_base(random, 1);
            shape.on(base, random)
        }
        8 | 9 => content_sum(random, 2),
        10 => copied_sum(random, 2),
        _ => input(random),
    }
}

/// An input of the negative-exponent property: a sum, a product, a power, a
/// negation, a difference or a quotient, each of whose operands is one of
/// the four shapes on a random base half of the time; with the position, the
/// shape and the base of each such operand.
fn negative_bases_input(random: &mut SplitMix64) -> (Expression, Vec<(usize, Shape, Expression)>) {
    let constructor = random.below(6);
    let arity = match constructor {
        0 | 1 => 1 + random.index(4),
        2 | 3 => 1,
        _ => 2,
    };
    let mut operands = Vec::with_capacity(arity);
    let mut shapes = Vec::new();
    for position in 0..arity {
        if random.chance(1, 2) {
            let shape = random.pick(&SHAPES);
            let base = shape_base(random, 2);
            operands.push(shape.on(base.clone(), random));
            shapes.push((position, shape, base));
        } else {
            operands.push(expression(random, DEPTH - 1));
        }
    }
    let input = match constructor {
        0 => Expression::Sum(operands),
        1 => Expression::Product(operands),
        2 => {
            let exponent = random.pick(&EXPONENTS);
            Expression::Power(Box::new(first(operands)), exponent)
        }
        3 => Expression::Negation(Box::new(first(operands))),
        _ => {
            let mut operands = operands.into_iter();
            let left = Box::new(operands.next().expect("a left operand"));
            let right = Box::new(operands.next().expect("a right operand"));
            if constructor == 4 {
                Expression::Difference(left, right)
            } else {
                Expression::Quotient(left, right)
            }
        }
    };
    (input, shapes)
}

fn first(operands: Vec<Expression>) -> Expression {
    operands.into_iter().next().expect("an operand")
}

/// The name of the constructor at the root of `input`.
fn constructor_name(input: &Expression) -> &'static str {
    match input {
        Expression::Number(..) => "number",
        Expression::Symbol(_) => "symbol",
        Expression::Sum(_) => "sum",
        Expression::Product(_) => "product",
        Expression::Power(..) => "power",
        Expression::Negation(_) => "negation",
        Expression::Difference(..) => "difference",
        Expression::Quotient(..) => "quotient",
    }
}

// ---------------------------------------------------------------------------
// Construction through the public constructors

/// The number `numerator / denominator`.
fn number(numerator: i64, denominator: i64, context: &mut Context) -> kalyx::Result<Term> {
    let value = Rational::new(
        Integer::from(numerator),
        Integer::from(denominator),
        context,
    )?;
    Term::number(value, context)
}

/// Builds the operands of `expression`, each with [`build`], and then its
/// root, with the operands in their given order; returns the operands and
/// the result.
fn construct(
    expression: &Expression,
    context: &mut Context,
    tally: &mut Tally,
) -> kalyx::Result<(Vec<Term>, Term)> {
    match expression {
        Expression::Number(numerator, denominator) => {
            Ok((Vec::new(), number(*numerator, *denominator, context)?))
        }
        Expression::Symbol(index) => Ok((Vec::new(), Term::symbol(NAMES[*index], context)?)),
        Expression::Sum(parts) => {
            let operands = build_all(parts, context, tally)?;
            count_scaled_sums(Join::Sum, &operands, tally);
            let result = Term::sum(&operands, context)?;
            Ok((operands, result))
        }
        Expression::Product(parts) => {
            let operands = build_all(parts, context, tally)?;
            count_scaled_sums(Join::Product, &operands, tally);
            let result = Term::product(&operands, context)?;
            Ok((operands, result))
        }
        Expression::Power(base, exponent) => {
            let base = build(base, context, tally)?;
            count_scaled_base(&base, *exponent, tally);
            let result = base.power(*exponent, context)?;
            Ok((vec![base], result))
        }
        Expression::Negation(operand) => {
            let operand = build(operand, context, tally)?;
            count_negated_sum(&operand, tally);
            let result = operand.negate(context)?;
            Ok((vec![operand], result))
        }
        Expression::Difference(left, right) => {
            let left = build(left, context, tally)?;
            let right = build(right, context, tally)?;
            let result = left.subtract(&right, context)?;
            Ok((vec![left, right], result))
        }
        Expression::Quotient(left, right) => {
            let left = build(left, context, tally)?;
            let right = build(right, context, tally)?;
            let result = left.divide(&right, context)?;
            Ok((vec![left, right], result))
        }
    }
}

/// Builds `expression` bottom-up through the public constructors, with the
/// operands in their given order, and checks at every constructor that $N$
/// of each operand is contained in $N$ of the result.
fn build(expression: &Expression, context: &mut Context, tally: &mut Tally) -> kalyx::Result<Term> {
    let (operands, result) = construct(expression, context, tally)?;
    if !operands.is_empty() {
        assert_keeps_negative_bases(&operands, &result);
        tally.add("constructors checked for N", 1);
    }
    Ok(result)
}

fn build_all(
    parts: &[Expression],
    context: &mut Context,
    tally: &mut Tally,
) -> kalyx::Result<Vec<Term>> {
    let mut terms = Vec::with_capacity(parts.len());
    for part in parts {
        terms.push(build(part, context, tally)?);
    }
    Ok(terms)
}

/// How [`combine`] joins terms.
#[derive(Clone, Copy)]
enum Join {
    Sum,
    Product,
}

impl Join {
    fn apply(
        self,
        terms: &[Term],
        context: &mut Context,
        tally: &mut Tally,
    ) -> kalyx::Result<Term> {
        count_scaled_sums(self, terms, tally);
        let result = match self {
            Self::Sum => Term::sum(terms, context)?,
            Self::Product => Term::product(terms, context)?,
        };
        if !terms.is_empty() {
            assert_keeps_negative_bases(terms, &result);
            tally.add("constructors checked for N", 1);
        }
        Ok(result)
    }
}

/// Counts the scaled sums among the operands of a sum or a product, read
/// through the accessors: for a sum, each group of two or more operands that
/// are sums with one primitive part, by the pattern of their contents; for a
/// product, a sum times numbers alone whose product is neither 0 nor 1, which
/// scales the sum, and a sum whose content is not 1 among two or more
/// operands that are not numbers.
fn count_scaled_sums(join: Join, operands: &[Term], tally: &mut Tally) {
    match join {
        Join::Sum => {
            let mut groups: Vec<Vec<&Term>> = Vec::new();
            for operand in operands.iter().filter(|operand| operand.as_sum().is_some()) {
                match groups
                    .iter_mut()
                    .find(|group| same_primitive(group[0], operand))
                {
                    Some(group) => group.push(operand),
                    None => groups.push(vec![operand]),
                }
            }
            for group in groups.iter().filter(|group| group.len() >= 2) {
                let mut contents: Vec<Fraction> = group.iter().map(|sum| content(sum)).collect();
                contents.sort_by(Fraction::order);
                tally.add(copies_pattern(&contents), 1);
            }
        }
        Join::Product => {
            let mut scale = Fraction::new(1, 1);
            let mut sums = 0;
            let mut contents_not_one = 0;
            let mut others = 0;
            for operand in operands {
                if let Some(value) = operand.as_number() {
                    scale = scale.times(&Fraction::of(value));
                } else if operand.as_sum().is_some() {
                    sums += 1;
                    if !content(operand).is_one() {
                        contents_not_one += 1;
                    }
                } else {
                    others += 1;
                }
            }
            if sums == 1 && others == 0 && !scale.is_zero() && !scale.is_one() {
                tally.add("sums scaled by a number", 1);
            }
            if contents_not_one > 0 && sums + others >= 2 {
                tally.add(
                    "sums whose content is not 1 among the factors of a product",
                    1,
                );
            }
        }
    }
}

/// The name of the pattern of the contents of scaled copies of one sum, in
/// increasing order: $[2s, -s, -s]$, $[2s, -s, 2s, -s]$ or another.
fn copies_pattern(contents: &[Fraction]) -> &'static str {
    // Whether `twice` is $-2$ times `once`.
    let doubled =
        |twice: &Fraction, once: &Fraction| twice.equals(&once.times(&Fraction::new(-2, 1)));
    match contents {
        [a, b, c] if (b.equals(c) && doubled(a, b)) || (a.equals(b) && doubled(c, a)) => {
            "operands [2s, -s, -s] of a sum"
        }
        [a, b, c, d] if a.equals(b) && c.equals(d) && (doubled(a, c) || doubled(c, a)) => {
            "operands [2s, -s, 2s, -s] of a sum"
        }
        _ => "other scaled copies of one sum among the operands of a sum",
    }
}

/// Counts a power of a sum whose content is not 1 to an exponent other than
/// 0 and 1, which takes the sum by its primitive part.
fn count_scaled_base(base: &Term, exponent: i64, tally: &mut Tally) {
    if base.as_sum().is_some() && exponent != 0 && exponent != 1 && !content(base).is_one() {
        tally.add("powers of sums whose content is not 1", 1);
    }
}

/// Counts the negation of a sum, which scales the sum by $-1$.
fn count_negated_sum(operand: &Term, tally: &mut Tally) {
    if operand.as_sum().is_some() {
        tally.add("sums scaled by a number", 1);
    }
}

/// Joins `terms` in a random order and a random grouping: a sum of the sums
/// of consecutive runs, or a product of their products, with now and then a
/// sum or a product of a single term.
fn combine(
    mut terms: Vec<Term>,
    join: Join,
    random: &mut SplitMix64,
    context: &mut Context,
    tally: &mut Tally,
) -> kalyx::Result<Term> {
    random.shuffle(&mut terms);
    if terms.len() < 2 || random.chance(1, 4) {
        return join.apply(&terms, context, tally);
    }
    // Two or more runs, so that each run is shorter than `terms`.
    let cut = 1 + random.index(terms.len() - 1);
    let mut runs: Vec<Vec<Term>> = Vec::new();
    let mut run = Vec::new();
    for (position, term) in terms.into_iter().enumerate() {
        if position == cut || (position > 0 && random.chance(1, 3)) {
            runs.push(std::mem::take(&mut run));
        }
        run.push(term);
    }
    runs.push(run);
    let mut parts = Vec::with_capacity(runs.len());
    for mut run in runs {
        let part = if run.len() == 1 && random.chance(3, 4) {
            run.pop().expect("a run of one term")
        } else {
            combine(run, join, random, context, tally)?
        };
        parts.push(part);
    }
    join.apply(&parts, context, tally)
}

/// Builds `expression` through the public constructors with a random order
/// and grouping of the operands of every sum and product, and with each
/// negation, difference and quotient built either by its method or by the
/// product, sum or power that defines it.
fn realize(
    expression: &Expression,
    random: &mut SplitMix64,
    context: &mut Context,
    tally: &mut Tally,
) -> kalyx::Result<Term> {
    match expression {
        Expression::Number(..) | Expression::Symbol(_) => build(expression, context, tally),
        Expression::Sum(parts) => {
            let terms = realize_all(parts, random, context, tally)?;
            combine(terms, Join::Sum, random, context, tally)
        }
        Expression::Product(parts) => {
            let terms = realize_all(parts, random, context, tally)?;
            combine(terms, Join::Product, random, context, tally)
        }
        Expression::Power(base, exponent) => {
            let base = realize(base, random, context, tally)?;
            count_scaled_base(&base, *exponent, tally);
            base.power(*exponent, context)
        }
        Expression::Negation(operand) => {
            let operand = realize(operand, random, context, tally)?;
            count_negated_sum(&operand, tally);
            let minus_one = number(-1, 1, context)?;
            match random.below(3) {
                0 => operand.negate(context),
                1 => Term::product(&[minus_one, operand], context),
                _ => Term::product(&[operand, minus_one], context),
            }
        }
        Expression::Difference(left, right) => {
            let left = realize(left, random, context, tally)?;
            let right = realize(right, random, context, tally)?;
            match random.below(3) {
                0 => left.subtract(&right, context),
                1 => {
                    let negated = right.negate(context)?;
                    combine(vec![left, negated], Join::Sum, random, context, tally)
                }
                _ => {
                    let minus_one = number(-1, 1, context)?;
                    let negated = Term::product(&[right, minus_one], context)?;
                    combine(vec![left, negated], Join::Sum, random, context, tally)
                }
            }
        }
        Expression::Quotient(left, right) => {
            let left = realize(left, random, context, tally)?;
            let right = realize(right, random, context, tally)?;
            if random.chance(1, 2) {
                left.divide(&right, context)
            } else {
                let inverse = right.power(-1, context)?;
                combine(vec![left, inverse], Join::Product, random, context, tally)
            }
        }
    }
}

fn realize_all(
    parts: &[Expression],
    random: &mut SplitMix64,
    context: &mut Context,
    tally: &mut Tally,
) -> kalyx::Result<Vec<Term>> {
    let mut terms = Vec::with_capacity(parts.len());
    for part in parts {
        terms.push(realize(part, random, context, tally)?);
    }
    Ok(terms)
}

/// [`build`] with the signature of a [`Construction`].
fn plain(
    expression: &Expression,
    _random: &mut SplitMix64,
    context: &mut Context,
    tally: &mut Tally,
) -> kalyx::Result<Term> {
    build(expression, context, tally)
}

/// A way to build an input: [`plain`] or [`realize`].
type Construction =
    fn(&Expression, &mut SplitMix64, &mut Context, &mut Tally) -> kalyx::Result<Term>;

/// Draws an input from `generate` and builds it with `construct`. An input
/// that fails with a division by zero must be undefined at every sample
/// point; it is drawn again.
fn draw(
    case: &mut Case,
    tally: &mut Tally,
    generate: fn(&mut SplitMix64) -> Expression,
    construct: Construction,
) -> (Expression, Term, Vec<Point>) {
    for _ in 0..ATTEMPTS {
        let input = generate(&mut case.random);
        case.note(&input);
        let points = points(&mut case.random);
        match construct(&input, &mut case.random, &mut case.context, tally) {
            Ok(term) => {
                tally.add("nodes of the terms", term.size());
                return (input, term, points);
            }
            Err(error) => {
                assert_division_by_zero(&error);
                assert_undefined(&input, &points);
                case.drawn_again(tally);
            }
        }
    }
    panic!("none of {ATTEMPTS} inputs was built without a division by zero");
}

fn assert_division_by_zero(error: &Error) {
    assert_eq!(
        error.kind(),
        ErrorKind::Fault(FaultKind::DivisionByZero),
        "an input failed with another error: {error}"
    );
}

// ---------------------------------------------------------------------------
// The model

/// A sample point: the values of `x`, `y` and `z`.
type Point = [Fraction; 3];

fn points(random: &mut SplitMix64) -> Vec<Point> {
    let mut list = Vec::with_capacity(POINTS);
    for _ in 0..POINTS {
        list.push([value(random), value(random), value(random)]);
    }
    list
}

fn value(random: &mut SplitMix64) -> Fraction {
    let (numerator, denominator) = random.pick(&VALUES);
    Fraction::new(numerator, denominator)
}

fn point_text(point: &Point) -> String {
    format!(
        "x = {}, y = {}, z = {}",
        point[0].text(),
        point[1].text(),
        point[2].text()
    )
}

/// The value of an input at `point`, or `None` where it is undefined: the
/// evaluation is strict, so an undefined operand leaves every expression
/// around it undefined, a factor 0 included, and $0^0 = 1$.
fn evaluate(expression: &Expression, point: &Point) -> Option<Fraction> {
    match expression {
        Expression::Number(numerator, denominator) => Some(Fraction::new(*numerator, *denominator)),
        Expression::Symbol(index) => Some(point[*index].clone()),
        Expression::Sum(parts) => {
            let mut total = Fraction::new(0, 1);
            for part in parts {
                total = total.plus(&evaluate(part, point)?);
            }
            Some(total)
        }
        Expression::Product(parts) => {
            let mut total = Fraction::new(1, 1);
            for part in parts {
                total = total.times(&evaluate(part, point)?);
            }
            Some(total)
        }
        Expression::Power(base, exponent) => evaluate(base, point)?.power(*exponent),
        Expression::Negation(operand) => Some(evaluate(operand, point)?.negated()),
        Expression::Difference(left, right) => {
            let left = evaluate(left, point)?;
            let right = evaluate(right, point)?;
            Some(left.plus(&right.negated()))
        }
        Expression::Quotient(left, right) => {
            let left = evaluate(left, point)?;
            let right = evaluate(right, point)?;
            Some(left.times(&right.inverse()?))
        }
    }
}

/// The value of a canonical term at `point`, read through its accessors, or
/// `None` where it is undefined, with the same strict rules.
fn evaluate_term(term: &Term, point: &Point) -> Option<Fraction> {
    match term.kind() {
        TermKind::Number => Some(Fraction::of(term.as_number().expect("a number"))),
        TermKind::Symbol => {
            let name = term.as_symbol().expect("a symbol");
            let index = NAMES
                .iter()
                .position(|candidate| *candidate == name)
                .unwrap_or_else(|| panic!("a symbol {name} that the generator does not use"));
            Some(point[index].clone())
        }
        TermKind::Power => {
            let (base, exponent) = term.as_power().expect("a power");
            evaluate_term(base, point)?.power(exponent)
        }
        TermKind::Product => {
            let (coefficient, factors) = term.as_product().expect("a product");
            let mut total = Fraction::of(coefficient);
            for factor in factors {
                total = total.times(&evaluate_term(factor, point)?);
            }
            Some(total)
        }
        TermKind::Sum => {
            let (constant, coefficients, cores) = term.as_sum().expect("a sum");
            assert_eq!(coefficients.len(), cores.len(), "a sum {}", render(term));
            let mut total = Fraction::of(constant);
            for (coefficient, core) in coefficients.iter().zip(cores) {
                let value = evaluate_term(core, point)?;
                total = total.plus(&Fraction::of(coefficient).times(&value));
            }
            Some(total)
        }
        other => panic!("a term of kind {other:?}"),
    }
}

/// Asserts that `term` agrees with `input` at every point: equal where the
/// input is defined, and undefined where the input is undefined.
fn agree(input: &Expression, term: &Term, points: &[Point], tally: &mut Tally) {
    for point in points {
        match (evaluate(input, point), evaluate_term(term, point)) {
            (Some(expected), Some(actual)) => {
                assert!(
                    expected.equals(&actual),
                    "at {}, the input is {} but the term {} is {}",
                    point_text(point),
                    expected.text(),
                    render(term),
                    actual.text()
                );
                tally.add("defined points", 1);
            }
            (None, None) => tally.add("undefined points", 1),
            (None, Some(actual)) => panic!(
                "at {}, the input is undefined but the term {} is {}",
                point_text(point),
                render(term),
                actual.text()
            ),
            (Some(expected), None) => panic!(
                "at {}, the input is {} but the term {} is undefined",
                point_text(point),
                expected.text(),
                render(term)
            ),
        }
    }
}

/// Asserts that `input`, whose construction failed with a division by
/// zero, is undefined at every point.
fn assert_undefined(input: &Expression, points: &[Point]) {
    for point in points {
        if let Some(value) = evaluate(input, point) {
            panic!(
                "the input failed with a division by zero, but at {} it is {}",
                point_text(point),
                value.text()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Structure, read through the accessors

/// Whether `left` and `right` have the same structure.
fn same(left: &Term, right: &Term) -> bool {
    if left.kind() != right.kind() {
        return false;
    }
    match left.kind() {
        TermKind::Number => left.as_number() == right.as_number(),
        TermKind::Symbol => left.as_symbol() == right.as_symbol(),
        TermKind::Power => match (left.as_power(), right.as_power()) {
            (Some((base, exponent)), Some((other_base, other_exponent))) => {
                exponent == other_exponent && same(base, other_base)
            }
            _ => false,
        },
        TermKind::Product => match (left.as_product(), right.as_product()) {
            (Some((coefficient, factors)), Some((other_coefficient, other_factors))) => {
                coefficient == other_coefficient && same_list(factors, other_factors)
            }
            _ => false,
        },
        TermKind::Sum => match (left.as_sum(), right.as_sum()) {
            (
                Some((constant, coefficients, cores)),
                Some((other_constant, other_coefficients, other_cores)),
            ) => {
                constant == other_constant
                    && coefficients == other_coefficients
                    && same_list(cores, other_cores)
            }
            _ => false,
        },
        other => panic!("a term of kind {other:?}"),
    }
}

fn same_list(left: &[Term], right: &[Term]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(term, other)| same(term, other))
}

/// The rank of the kind of `term` in the total order, from the table of the
/// contract.
fn rank(term: &Term) -> u8 {
    match term.kind() {
        TermKind::Number => 0,
        TermKind::Symbol => 2,
        TermKind::Call => 3,
        TermKind::Power => 4,
        TermKind::Product => 5,
        TermKind::Sum => 6,
        other => panic!("a term of kind {other:?}"),
    }
}

/// The total order of the contract, written here: by rank, then numbers by
/// value, symbols by the bytes of their names, powers by base and then
/// exponent, products by their factors one by one, the number of factors
/// and then the coefficient, and sums by their monomials one by one (core,
/// then coefficient), the number of monomials and then the constant.
fn order(left: &Term, right: &Term) -> Ordering {
    let ranks = rank(left).cmp(&rank(right));
    if ranks != Ordering::Equal {
        return ranks;
    }
    match left.kind() {
        TermKind::Number => rational_order(
            left.as_number().expect("a number"),
            right.as_number().expect("a number"),
        ),
        TermKind::Symbol => {
            let name = left.as_symbol().expect("a symbol");
            let other = right.as_symbol().expect("a symbol");
            name.as_bytes().cmp(other.as_bytes())
        }
        TermKind::Power => {
            let (base, exponent) = left.as_power().expect("a power");
            let (other_base, other_exponent) = right.as_power().expect("a power");
            order(base, other_base).then(exponent.cmp(&other_exponent))
        }
        TermKind::Product => {
            let (coefficient, factors) = left.as_product().expect("a product");
            let (other_coefficient, other_factors) = right.as_product().expect("a product");
            order_lists(factors, other_factors)
                .then(factors.len().cmp(&other_factors.len()))
                .then_with(|| rational_order(coefficient, other_coefficient))
        }
        TermKind::Sum => {
            let (constant, coefficients, cores) = left.as_sum().expect("a sum");
            let (other_constant, other_coefficients, other_cores) = right.as_sum().expect("a sum");
            let monomials = cores.iter().zip(coefficients);
            let other_monomials = other_cores.iter().zip(other_coefficients);
            for ((core, coefficient), (other_core, other_coefficient)) in
                monomials.zip(other_monomials)
            {
                let step = order(core, other_core)
                    .then_with(|| rational_order(coefficient, other_coefficient));
                if step != Ordering::Equal {
                    return step;
                }
            }
            cores
                .len()
                .cmp(&other_cores.len())
                .then_with(|| rational_order(constant, other_constant))
        }
        other => panic!("a term of kind {other:?}"),
    }
}

fn order_lists(left: &[Term], right: &[Term]) -> Ordering {
    for (term, other) in left.iter().zip(right) {
        let step = order(term, other);
        if step != Ordering::Equal {
            return step;
        }
    }
    Ordering::Equal
}

fn rational_order(left: &Rational, right: &Rational) -> Ordering {
    Fraction::of(left).order(&Fraction::of(right))
}

/// The public order of `left` and `right`, which must be the order of the
/// contract written here.
fn compare(left: &Term, right: &Term, context: &mut Context) -> Ordering {
    let public = left.compare(right, context).unwrap();
    assert_eq!(
        public,
        order(left, right),
        "compare and the order of the contract differ on {} and {}",
        render(left),
        render(right)
    );
    public
}

/// Every node of `term`, a shared subterm once for each occurrence.
fn nodes(term: &Term) -> Vec<Term> {
    let mut list = Vec::new();
    let mut stack = vec![term.clone()];
    while let Some(node) = stack.pop() {
        stack.extend(node.children().iter().cloned());
        list.push(node);
    }
    list
}

/// The content of a sum, as the contract defines it: the coefficient of its
/// first monomial, in the stored order of its cores, whose coefficient is not
/// 0, or its constant when every monomial has the coefficient 0, as the
/// witness monomial does. [`check_shape`] asserts that it is never 0.
fn content(sum: &Term) -> Fraction {
    let (constant, coefficients, _) = sum.as_sum().expect("a sum");
    let first = coefficients
        .iter()
        .find(|coefficient| !coefficient.is_zero())
        .unwrap_or(constant);
    Fraction::of(first)
}

/// The content of `term` when it is a sum, and 1 for any other term, which a
/// product or a power takes as it is.
fn content_of(term: &Term) -> Fraction {
    if term.as_sum().is_some() {
        content(term)
    } else {
        Fraction::new(1, 1)
    }
}

/// Whether the sums `left` and `right` have the same cores in the same order,
/// and the constant and each coefficient of `left` times `left_scale` equal
/// those of `right` times `right_scale`; false when either is not a sum.
fn proportional(left: &Term, right: &Term, left_scale: &Fraction, right_scale: &Fraction) -> bool {
    let (
        Some((left_constant, left_coefficients, left_cores)),
        Some((right_constant, right_coefficients, right_cores)),
    ) = (left.as_sum(), right.as_sum())
    else {
        return false;
    };
    let scaled_equal = |left: &Rational, right: &Rational| {
        Fraction::of(left)
            .times(left_scale)
            .equals(&Fraction::of(right).times(right_scale))
    };
    same_list(left_cores, right_cores)
        && left_coefficients.len() == right_coefficients.len()
        && scaled_equal(left_constant, right_constant)
        && left_coefficients
            .iter()
            .zip(right_coefficients)
            .all(|(left, right)| scaled_equal(left, right))
}

/// Whether `result` is the sum `sum` scaled by `scale`: a sum over the cores
/// of `sum` in their order whose constant and coefficients are those of `sum`
/// times `scale`.
fn is_scaled(result: &Term, sum: &Term, scale: &Fraction) -> bool {
    proportional(result, sum, &Fraction::new(1, 1), scale)
}

/// Whether `candidate` is the primitive part $p = s / c$ of `sum`, a sum $s$
/// with the content $c$: $s$ is $p$ scaled by $c$, so $p$ has the cores of
/// $s$ and the content 1.
fn is_primitive_part(candidate: &Term, sum: &Term) -> bool {
    is_scaled(sum, candidate, &content(sum))
}

/// Whether `candidate` is how a product or a power takes `base`: the
/// primitive part of a sum, and any other term itself.
fn is_base_part(candidate: &Term, base: &Term) -> bool {
    if base.as_sum().is_some() {
        is_primitive_part(candidate, base)
    } else {
        same(candidate, base)
    }
}

/// Whether `left` and `right` have one primitive part: two sums over the
/// same cores whose parts divided by their contents are equal, or two other
/// terms of the same structure.
fn same_primitive(left: &Term, right: &Term) -> bool {
    match (left.as_sum(), right.as_sum()) {
        (Some(_), Some(_)) => proportional(left, right, &content(right), &content(left)),
        _ => same(left, right),
    }
}

/// $N(t)$: the bases of the powers with a negative exponent anywhere in
/// `term`, nested ones included, without repetitions. A base that is a sum
/// stands for its primitive part: [`contains`] compares sums by their
/// primitive parts, which this file computes from the accessors, so two
/// sums with one primitive part are one element.
fn negative_set(term: &Term) -> Vec<Term> {
    let mut bases: Vec<Term> = Vec::new();
    for node in nodes(term) {
        if let Some((base, exponent)) = node.as_power()
            && exponent < 0
            && !contains(&bases, base)
        {
            bases.push(base.clone());
        }
    }
    bases
}

/// Whether `set`, a set of bases, holds `term`, a sum compared by its
/// primitive part.
fn contains(set: &[Term], term: &Term) -> bool {
    set.iter().any(|member| same_primitive(member, term))
}

/// $\max N$: the elements of `set` that do not occur with a negative exponent
/// inside another element.
fn maximal(set: &[Term]) -> Vec<Term> {
    let mut result = Vec::new();
    for candidate in set {
        let inside = set.iter().any(|other| {
            !same_primitive(other, candidate) && contains(&negative_set(other), candidate)
        });
        if !inside {
            result.push(candidate.clone());
        }
    }
    result
}

/// The key of a factor: its base and whether its exponent is negative. A
/// factor that is not a power is its own base with the exponent 1, and a one
/// $(b^{-1})^0$ has the base $b^{-1}$ with a nonnegative exponent.
fn key(factor: &Term) -> (Term, bool) {
    match factor.as_power() {
        Some((base, exponent)) => (base.clone(), exponent < 0),
        None => (factor.clone(), false),
    }
}

/// The merge condition of a power of a power $(b^j)^k$: $jk < 0$, or
/// $j, k \ge 0$, or $j = 0$.
fn merges(j: i64, k: i64) -> bool {
    i128::from(j) * i128::from(k) < 0 || (j >= 0 && k >= 0) || j == 0
}

fn is_one_value(value: &Rational) -> bool {
    *value == Rational::from(1)
}

/// Whether `term` is the power `exponent` of `base`.
fn is_power_of(term: &Term, base: &Term, exponent: i64) -> bool {
    term.as_power()
        .is_some_and(|(inner, power)| power == exponent && same(inner, base))
}

/// Whether `term` is the power `exponent` of `base` as a power takes it: of
/// the primitive part of a sum, and of any other term itself.
fn is_power_of_part(term: &Term, base: &Term, exponent: i64) -> bool {
    term.as_power()
        .is_some_and(|(inner, power)| power == exponent && is_base_part(inner, base))
}

/// Whether `result` is $c^k p^k$ for `base`, a sum with the content $c$ and
/// the primitive part $p$, or a symbol with $c = 1$ and $p$ the symbol, and
/// the exponent $k$, with `scale` $= c^k$: the power $p^k$ itself when
/// $c^k = 1$, and otherwise the product of $c^k$ and the single factor $p^k$.
fn is_scaled_power(result: &Term, scale: &Fraction, base: &Term, exponent: i64) -> bool {
    if scale.is_one() {
        return is_power_of_part(result, base, exponent);
    }
    result.as_product().is_some_and(|(coefficient, factors)| {
        Fraction::of(coefficient).equals(scale)
            && factors.len() == 1
            && is_power_of_part(&factors[0], base, exponent)
    })
}

/// Whether `term` is the one $(b^{-1})^0$ of `base`.
fn is_one_of(term: &Term, base: &Term) -> bool {
    term.as_power()
        .is_some_and(|(inner, exponent)| exponent == 0 && is_power_of(inner, base, -1))
}

/// The base $b$ that a one $(b^{-1})^0$ keeps, or `None` for any other term.
fn one_base(term: &Term) -> Option<Term> {
    let (inner, exponent) = term.as_power()?;
    let (base, inverse) = inner.as_power()?;
    (exponent == 0 && inverse == -1).then(|| base.clone())
}

/// The ones $(b^{-1})^0$ among the nodes of `term`.
fn ones(term: &Term) -> Vec<Term> {
    let mut list = Vec::new();
    for node in nodes(term) {
        if one_base(&node).is_some() {
            list.push(node);
        }
    }
    list
}

/// The bases of a witness core, a reciprocal $b^{-1}$ or a product of
/// reciprocals with the coefficient 1, or `None` for any other core.
fn reciprocal_bases(core: &Term) -> Option<Vec<Term>> {
    if let Some((base, -1)) = core.as_power() {
        return Some(vec![base.clone()]);
    }
    let (coefficient, factors) = core.as_product()?;
    if !is_one_value(coefficient) || factors.len() < 2 {
        return None;
    }
    let mut bases = Vec::with_capacity(factors.len());
    for factor in factors {
        match factor.as_power() {
            Some((base, -1)) => bases.push(base.clone()),
            _ => return None,
        }
    }
    Some(bases)
}

fn is_identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    match bytes.next() {
        Some(first) if first.is_ascii_alphabetic() || first == b'_' => {
            bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        }
        _ => false,
    }
}

/// A text of `term` for the messages of failed checks, read through the
/// accessors as `power(base, k)`, `product(c; [factors])` and
/// `sum(c; coefficient*core, ...)`; it is not the display grammar.
fn render(term: &Term) -> String {
    match term.kind() {
        TermKind::Number => term.as_number().expect("a number").to_string(),
        TermKind::Symbol => term.as_symbol().expect("a symbol").to_string(),
        TermKind::Power => {
            let (base, exponent) = term.as_power().expect("a power");
            format!("power({}, {exponent})", render(base))
        }
        TermKind::Product => {
            let (coefficient, factors) = term.as_product().expect("a product");
            format!("product({coefficient}; {})", list_text(factors))
        }
        TermKind::Sum => {
            let (constant, coefficients, cores) = term.as_sum().expect("a sum");
            let monomials: Vec<String> = coefficients
                .iter()
                .zip(cores)
                .map(|(coefficient, core)| format!("{coefficient}*{}", render(core)))
                .collect();
            format!("sum({constant}; {})", monomials.join(", "))
        }
        other => format!("{other:?}"),
    }
}

fn list_text(terms: &[Term]) -> String {
    let list: Vec<String> = terms.iter().map(render).collect();
    format!("[{}]", list.join(", "))
}

// ---------------------------------------------------------------------------
// Checks of the canonical forms

/// Asserts that `left` and `right` are one term: the same structure,
/// `compare` gives `Equal` both ways, `equals` holds, and the display bytes
/// are the same.
fn assert_same_term(left: &Term, right: &Term, context: &mut Context, what: &str) {
    assert!(
        same(left, right),
        "{what}: {} and {} differ in structure",
        render(left),
        render(right)
    );
    assert_eq!(
        left.compare(right, context).unwrap(),
        Ordering::Equal,
        "{what}: compare"
    );
    assert_eq!(
        right.compare(left, context).unwrap(),
        Ordering::Equal,
        "{what}: compare"
    );
    assert!(left.equals(right, context).unwrap(), "{what}: equals");
    let text = left.display(context).unwrap();
    let other = right.display(context).unwrap();
    assert_eq!(text.as_bytes(), other.as_bytes(), "{what}: display");
}

/// Asserts $N(o) \subseteq N(\mathrm{result})$ for every operand $o$, both
/// sets computed here.
fn assert_keeps_negative_bases(operands: &[Term], result: &Term) {
    let kept = negative_set(result);
    for operand in operands {
        for base in negative_set(operand) {
            assert!(
                contains(&kept, &base),
                "the base {} of the operand {} is not in N of the result {}",
                render(&base),
                render(operand),
                render(result)
            );
        }
    }
}

/// Asserts that `negative_bases` gives $N$ of `term` as computed here,
/// sorted strictly by `compare`, and that `has_negative_power` holds at
/// exactly the nodes whose $N$ is not empty.
fn assert_negative_bases(term: &Term, context: &mut Context) {
    let expected = negative_set(term);
    let listed = term.negative_bases(context).unwrap();
    assert_eq!(
        listed.len(),
        expected.len(),
        "negative_bases of {} gives {}, not {}",
        render(term),
        list_text(&listed),
        list_text(&expected)
    );
    for base in &listed {
        assert!(
            contains(&expected, base),
            "negative_bases of {} gives {}, which is not in N",
            render(term),
            render(base)
        );
    }
    for pair in listed.windows(2) {
        assert_eq!(
            compare(&pair[0], &pair[1], context),
            Ordering::Less,
            "negative_bases of {} is not sorted strictly",
            render(term)
        );
    }
    for node in nodes(term) {
        assert_eq!(
            node.has_negative_power(),
            !negative_set(&node).is_empty(),
            "has_negative_power of {}",
            render(&node)
        );
    }
}

/// Asserts that the bases of a witness do not occur with a negative exponent
/// inside one another.
fn assert_not_nested(bases: &[Term], text: &str) {
    for (index, base) in bases.iter().enumerate() {
        for (other_index, other) in bases.iter().enumerate() {
            assert!(
                index == other_index || !contains(&negative_set(other), base),
                "in {text}, the base {} occurs with a negative exponent inside {}",
                render(base),
                render(other)
            );
        }
    }
}

/// The elimination of 0 and 1 at every node of `term`: no exponent 1, the
/// exponent 0 only in a one $(b^{-1})^0$, no factor that is a number, no
/// product with the coefficient 1 and a single factor, only reciprocals with
/// the coefficient 0, no sum of fewer than two parts, no core that is a
/// number, and no monomial with the coefficient 0 but one witness monomial.
fn check_eliminated(term: &Term) {
    for node in nodes(term) {
        let text = render(&node);
        if let Some((_, exponent)) = node.as_power() {
            assert_ne!(exponent, 1, "the exponent 1 is left in {text}");
            assert!(
                exponent != 0 || one_base(&node).is_some(),
                "the exponent 0 is left in {text}, which is not a one"
            );
        }
        if let Some((coefficient, factors)) = node.as_product() {
            assert!(!factors.is_empty(), "the product {text} has no factor");
            assert!(
                factors.len() > 1 || !is_one_value(coefficient),
                "the product {text} has the coefficient 1 and a single factor"
            );
            for factor in factors {
                assert!(
                    factor.as_number().is_none(),
                    "the product {text} has a number among its factors"
                );
                assert!(
                    !coefficient.is_zero() || is_power_of_exponent(factor, -1),
                    "the product {text} has the coefficient 0 and a factor that is not a reciprocal"
                );
            }
        }
        if let Some((constant, coefficients, cores)) = node.as_sum() {
            let parts = cores.len() + usize::from(!constant.is_zero());
            assert!(parts >= 2, "the sum {text} has fewer than two parts");
            let mut witnesses = 0;
            for (coefficient, core) in coefficients.iter().zip(cores) {
                assert!(
                    core.as_number().is_none(),
                    "the sum {text} has a number among its cores"
                );
                if coefficient.is_zero() {
                    witnesses += 1;
                    assert!(
                        reciprocal_bases(core).is_some(),
                        "the sum {text} has a monomial with the coefficient 0 that is not a witness"
                    );
                }
            }
            assert!(
                witnesses <= 1,
                "the sum {text} has two monomials with the coefficient 0"
            );
        }
    }
}

fn is_power_of_exponent(term: &Term, exponent: i64) -> bool {
    term.as_power().is_some_and(|(_, power)| power == exponent)
}

/// The canonical shape of every node of `term`, as the contract lists it for
/// numbers, symbols, powers, products and sums, with the elimination of 0
/// and 1: in particular, no core of a sum is a sum, and every sum that is a
/// factor of a product or the base of a power is primitive, with the
/// content 1.
fn check_shape(term: &Term) {
    check_eliminated(term);
    for node in nodes(term) {
        let text = render(&node);
        match node.kind() {
            TermKind::Number => {
                let value = node.as_number().expect("a number");
                assert!(
                    value.denominator().is_positive(),
                    "the number {text} has a denominator that is not positive"
                );
            }
            TermKind::Symbol => {
                let name = node.as_symbol().expect("a symbol");
                assert!(
                    is_identifier(name) && !RESERVED.contains(&name),
                    "the symbol {text} is not a valid name"
                );
            }
            TermKind::Power => {
                let (base, exponent) = node.as_power().expect("a power");
                assert!(
                    !matches!(base.kind(), TermKind::Number | TermKind::Product),
                    "the power {text} has a number or a product as its base"
                );
                if base.as_sum().is_some() {
                    assert!(
                        content(base).is_one(),
                        "the power {text} has a sum base whose content is {}, not 1",
                        content(base).text()
                    );
                }
                if let Some((_, inner)) = base.as_power() {
                    assert!(
                        !merges(inner, exponent),
                        "the power of a power {text} meets the merge condition"
                    );
                }
            }
            TermKind::Product => check_product_shape(&node, &text),
            TermKind::Sum => check_sum_shape(&node, &text),
            other => panic!("a term of kind {other:?}"),
        }
    }
}

fn check_product_shape(node: &Term, text: &str) {
    let (coefficient, factors) = node.as_product().expect("a product");
    for factor in factors {
        assert!(
            factor.as_product().is_none(),
            "the product {text} has a product among its factors"
        );
        if factor.as_sum().is_some() {
            assert!(
                content(factor).is_one(),
                "the product {text} has a sum factor whose content is {}, not 1",
                content(factor).text()
            );
        }
    }
    assert!(
        factors.len() > 1 || factors.iter().all(|factor| factor.as_sum().is_none()),
        "the product {text} is a number times a single sum, which it does not scale"
    );
    for pair in factors.windows(2) {
        let (base, negative) = key(&pair[0]);
        let (other_base, other_negative) = key(&pair[1]);
        assert_eq!(
            order(&base, &other_base).then(negative.cmp(&other_negative)),
            Ordering::Less,
            "the keys of the factors of {text} do not increase strictly"
        );
    }
    if coefficient.is_zero() {
        let mut bases = Vec::with_capacity(factors.len());
        for factor in factors {
            let (base, _) = factor.as_power().expect("a reciprocal");
            bases.push(base.clone());
        }
        assert_not_nested(&bases, text);
        return;
    }
    for (index, factor) in factors.iter().enumerate() {
        let Some(kept) = one_base(factor) else {
            continue;
        };
        for (other_index, other) in factors.iter().enumerate() {
            assert!(
                index == other_index || !contains(&negative_set(other), &kept),
                "the one {} of {text} keeps a base that the factor {} holds",
                render(factor),
                render(other)
            );
        }
    }
}

fn check_sum_shape(node: &Term, text: &str) {
    let (_, coefficients, cores) = node.as_sum().expect("a sum");
    assert_eq!(coefficients.len(), cores.len(), "the sum {text}");
    assert!(!content(node).is_zero(), "the sum {text} has the content 0");
    for pair in cores.windows(2) {
        assert_eq!(
            order(&pair[0], &pair[1]),
            Ordering::Less,
            "the cores of {text} do not increase strictly"
        );
    }
    for (index, (coefficient, core)) in coefficients.iter().zip(cores).enumerate() {
        if let Some((inner, _)) = core.as_product() {
            assert!(
                is_one_value(inner),
                "the sum {text} has a product core with a coefficient other than 1"
            );
        }
        assert!(
            core.as_sum().is_none(),
            "the sum {text} has a sum among its cores"
        );
        if coefficient.is_zero() {
            let bases = reciprocal_bases(core).expect("a witness core");
            assert_not_nested(&bases, text);
            for (other_index, other) in cores.iter().enumerate() {
                for base in &bases {
                    assert!(
                        index == other_index || !contains(&negative_set(other), base),
                        "the witness of {text} keeps the base {}, which the core {} holds",
                        render(base),
                        render(other)
                    );
                }
            }
        }
    }
}

/// Asserts that `result` is the ones $(b^{-1})^0$ of `bases`: the number 1
/// for none, the one itself for a single base, and otherwise their product
/// with the coefficient 1.
fn assert_ones(result: &Term, bases: &[Term], what: &str) {
    let kept = match bases {
        [] => result.as_number().is_some_and(is_one_value),
        [base] => is_one_of(result, base),
        _ => result.as_product().is_some_and(|(coefficient, factors)| {
            is_one_value(coefficient)
                && factors.len() == bases.len()
                && factors
                    .iter()
                    .all(|factor| bases.iter().any(|base| is_one_of(factor, base)))
        }),
    };
    assert!(
        kept,
        "{what} is {}, not the ones of {}",
        render(result),
        list_text(bases)
    );
}

/// Asserts that `result` is the zero witness of `bases`, the number 0 for
/// none and otherwise the product of their reciprocals with the coefficient
/// 0.
fn assert_zero_witness(result: &Term, bases: &[Term], what: &str) {
    let kept = match bases {
        [] => result.as_number().is_some_and(Rational::is_zero),
        _ => result.as_product().is_some_and(|(coefficient, factors)| {
            coefficient.is_zero()
                && factors.len() == bases.len()
                && factors
                    .iter()
                    .all(|factor| bases.iter().any(|base| is_power_of(factor, base, -1)))
        }),
    };
    assert!(
        kept,
        "{what} is {}, not the zero witness of {}",
        render(result),
        list_text(bases)
    );
}

/// Asserts that a shape on a symbol or a sum `base` is kept as written, a
/// sum $b = c \cdot p$ by its content $c$ and its primitive part $p$, and a
/// symbol $b$ as itself, with $c = 1$ and $p = b$: $b^2 \cdot b^{-1}$ as the
/// two factors $p^2$ and $p^{-1}$ with the coefficient $c$, $b \cdot b^{-1}$
/// as the two factors $p$ and $p^{-1}$ with the coefficient 1,
/// $0 \cdot b^{-1}$ as the zero witness $0 \cdot p^{-1}$, and $(b^{-1})^0$
/// as the one $(p^{-1})^0$.
fn assert_kept_as_written(term: &Term, shape: Shape, base: &Term) {
    // A product with the coefficient `scale` whose factors are, in this
    // order, the base as a product takes it for `None` and its power `k`
    // for `Some(k)`.
    let product_of = |scale: &Fraction, expected: &[Option<i64>]| {
        term.as_product().is_some_and(|(coefficient, factors)| {
            Fraction::of(coefficient).equals(scale)
                && factors.len() == expected.len()
                && factors
                    .iter()
                    .zip(expected)
                    .all(|(factor, power)| match power {
                        Some(exponent) => is_power_of_part(factor, base, *exponent),
                        None => is_base_part(factor, base),
                    })
        })
    };
    let kept = match shape {
        Shape::SquareTimesInverse => product_of(&content_of(base), &[Some(2), Some(-1)]),
        Shape::BaseTimesInverse => product_of(&Fraction::new(1, 1), &[None, Some(-1)]),
        Shape::ZeroTimesInverse => product_of(&Fraction::new(0, 1), &[Some(-1)]),
        Shape::InverseToTheZero => term
            .as_power()
            .is_some_and(|(inner, exponent)| exponent == 0 && is_power_of_part(inner, base, -1)),
    };
    assert!(
        kept,
        "{} on the base {} gives {}, which is not kept as written",
        shape.name(),
        render(base),
        render(term)
    );
}

/// Asserts that `result` is the sum `sum` scaled by `scale`, a number other
/// than 0 and 1: a sum over the cores of `sum` in their order, whose constant
/// and coefficients are those of `sum` times `scale`.
fn assert_scaled(result: &Term, sum: &Term, scale: &Fraction, what: &str) {
    assert!(
        is_scaled(result, sum, scale),
        "{what}: {} times {} is {}, not the scaled sum",
        scale.text(),
        render(sum),
        render(result)
    );
}

/// What the contract makes of a power, worked out here from its base.
enum Expected {
    /// `Fault(DivisionByZero)`.
    DivisionByZero,
    /// The number of this value.
    Value(Fraction),
    /// This term.
    Same(Term),
    /// The ones $(b^{-1})^0$ of these bases, as [`assert_ones`] states.
    Ones(Vec<Term>),
    /// The power node of this base and exponent.
    Power(Term, i64),
    /// $c^k p^k$ for a sum with the content $c$ and the primitive part $p$:
    /// the value $c^k$, the sum and $k$, as [`is_scaled_power`] states.
    ScaledPower(Fraction, Term, i64),
}

/// The power `base^exponent` by the rules of powers: a number strictly, the
/// exponent 1 the base, the exponent 0 the ones of $\max N$ of the base, a
/// product $c \prod f$ as the product of $c^k$ and the $f^k$, a sum
/// $s = c \cdot p$ with its content $c$ and its primitive part $p$ as
/// $c^k p^k$, and any other base by [`other_power`].
fn expected_power(
    base: &Term,
    exponent: i64,
    context: &mut Context,
    tally: &mut Tally,
) -> Expected {
    if let Some(value) = base.as_number() {
        tally.add("numeric bases", 1);
        return match Fraction::of(value).power(exponent) {
            Some(power) => Expected::Value(power),
            None => Expected::DivisionByZero,
        };
    }
    if exponent == 1 {
        tally.add("exponent 1", 1);
        return Expected::Same(base.clone());
    }
    if exponent == 0 {
        let bases = maximal(&negative_set(base));
        tally.add(
            if bases.is_empty() {
                "exponent 0 giving 1"
            } else {
                "exponent 0 giving ones"
            },
            1,
        );
        return Expected::Ones(bases);
    }
    if base.as_sum().is_some() {
        let content = content(base);
        let scale = content
            .power(exponent)
            .expect("the content of a sum is not 0");
        tally.add(
            if content.is_one() {
                "powers of sums whose content is 1"
            } else if scale.is_one() {
                "powers of sums whose content is not 1 but whose power is 1"
            } else {
                "powers of sums with a scaled power of the content"
            },
            1,
        );
        return Expected::ScaledPower(scale, base.clone(), exponent);
    }
    let Some((coefficient, factors)) = base.as_product() else {
        return other_power(base, exponent, tally);
    };
    if coefficient.is_zero() && exponent < 0 {
        tally.add("negative powers of products with the coefficient 0", 1);
        return Expected::DivisionByZero;
    }
    tally.add("powers of products", 1);
    let scalar = coefficient.power(exponent, context).unwrap();
    let mut parts = vec![Term::number(scalar, context).unwrap()];
    for factor in factors {
        let power = factor.power(exponent, context).unwrap();
        let what = format!("the factor {} to the power {exponent}", render(factor));
        assert_expected(&power, &other_power(factor, exponent, tally), &what);
        parts.push(power);
    }
    Expected::Same(Term::product(&parts, context).unwrap())
}

/// The power of a base that is neither a number nor a product: while the
/// base is a power $b^j$ that meets the merge condition with the exponent
/// $k$, it becomes $b$ with the exponent $jk$; then the exponent 1 gives the
/// base, the exponent 0 the ones of $\max N$ of the base, and any other
/// exponent a power node.
fn other_power(base: &Term, exponent: i64, tally: &mut Tally) -> Expected {
    let mut base = base.clone();
    let mut exponent = exponent;
    while let Some((inner, j)) = mergeable(&base, exponent) {
        exponent = j.checked_mul(exponent).expect("a small exponent");
        base = inner;
        tally.add("merged powers of powers", 1);
    }
    match exponent {
        1 => Expected::Same(base),
        0 => Expected::Ones(maximal(&negative_set(&base))),
        _ => {
            if base.as_power().is_some() {
                tally.add("powers of powers kept apart", 1);
            }
            Expected::Power(base, exponent)
        }
    }
}

/// The base $b$ and the exponent $j$ of `base`, when it is a power $b^j$ that
/// meets the merge condition with `exponent`.
fn mergeable(base: &Term, exponent: i64) -> Option<(Term, i64)> {
    let (inner, j) = base.as_power()?;
    merges(j, exponent).then(|| (inner.clone(), j))
}

fn assert_expected(result: &Term, expected: &Expected, what: &str) {
    match expected {
        Expected::DivisionByZero => {
            panic!("{what} is {}, not a division by zero", render(result))
        }
        Expected::Value(value) => {
            let actual = result
                .as_number()
                .unwrap_or_else(|| panic!("{what} is {}, not a number", render(result)));
            assert!(
                Fraction::of(actual).equals(value),
                "{what} is {actual}, not {}",
                value.text()
            );
        }
        Expected::Same(term) => assert!(
            same(result, term),
            "{what} is {}, not {}",
            render(result),
            render(term)
        ),
        Expected::Ones(bases) => assert_ones(result, bases, what),
        Expected::Power(base, exponent) => assert!(
            is_power_of(result, base, *exponent),
            "{what} is {}, not the power {exponent} of {}",
            render(result),
            render(base)
        ),
        Expected::ScaledPower(scale, sum, exponent) => assert!(
            is_scaled_power(result, scale, sum, *exponent),
            "{what} is {}, not {} times the power {exponent} of the primitive part of {}",
            render(result),
            scale.text(),
            render(sum)
        ),
    }
}

/// Rebuilds `term` bottom-up through the public constructors from the parts
/// that its accessors give, in their stored order or reversed.
fn rebuild(term: &Term, reversed: bool, context: &mut Context) -> Term {
    match term.kind() {
        TermKind::Number => Term::number(term.as_number().unwrap().clone(), context).unwrap(),
        TermKind::Symbol => Term::symbol(term.as_symbol().unwrap(), context).unwrap(),
        TermKind::Power => {
            let (base, exponent) = term.as_power().unwrap();
            rebuild(base, reversed, context)
                .power(exponent, context)
                .unwrap()
        }
        TermKind::Product => {
            let (coefficient, factors) = term.as_product().unwrap();
            let mut parts = vec![Term::number(coefficient.clone(), context).unwrap()];
            for factor in factors {
                parts.push(rebuild(factor, reversed, context));
            }
            if reversed {
                parts.reverse();
            }
            Term::product(&parts, context).unwrap()
        }
        TermKind::Sum => {
            let (constant, coefficients, cores) = term.as_sum().unwrap();
            let mut parts = vec![Term::number(constant.clone(), context).unwrap()];
            for (coefficient, core) in coefficients.iter().zip(cores) {
                let coefficient = Term::number(coefficient.clone(), context).unwrap();
                let core = rebuild(core, reversed, context);
                parts.push(Term::product(&[coefficient, core], context).unwrap());
            }
            if reversed {
                parts.reverse();
            }
            Term::sum(&parts, context).unwrap()
        }
        other => panic!("a term of kind {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The properties

/// Uniqueness: every order and grouping of the operands of the sums and
/// products of an input, with negation, difference and quotient built by
/// their methods or by the constructors that define them, gives one term:
/// the same structure, `compare` gives `Equal` both ways, and the display
/// bytes are the same. The term agrees with the model. The inputs hold
/// several scaled copies of one sum $s$, such as $[2s, -s, -s]$ and
/// $[2s, -s, 2s, -s]$, so that the groupings $(2s - s) - s$ and
/// $2s - s - s$, or $(2s - s) + (2s - s)$ and $2s - s + 2s - s$, meet, and
/// sums whose content is not 1 as factors and bases.
fn uniqueness_case(case: &mut Case, tally: &mut Tally) {
    for _ in 0..ATTEMPTS {
        let input = input(&mut case.random);
        case.note(&input);
        let points = points(&mut case.random);
        let mut outcomes = vec![build(&input, &mut case.context, tally)];
        for _ in 0..REGROUPINGS {
            outcomes.push(realize(&input, &mut case.random, &mut case.context, tally));
        }
        let failures = outcomes.iter().filter(|outcome| outcome.is_err()).count();
        if failures == outcomes.len() {
            for error in outcomes.iter().filter_map(|outcome| outcome.as_ref().err()) {
                assert_division_by_zero(error);
            }
            assert_undefined(&input, &points);
            case.drawn_again(tally);
            continue;
        }
        if failures != 0 {
            let texts: Vec<String> = outcomes
                .iter()
                .map(|outcome| match outcome {
                    Ok(term) => render(term),
                    Err(error) => format!("error {:?}", error.kind()),
                })
                .collect();
            panic!(
                "some orders and groupings failed and others did not: {}",
                texts.join(" | ")
            );
        }
        let terms: Vec<Term> = outcomes.into_iter().map(Result::unwrap).collect();
        tally.add("nodes of the terms", terms[0].size());
        agree(&input, &terms[0], &points, tally);
        for other in &terms[1..] {
            assert_same_term(
                &terms[0],
                other,
                &mut case.context,
                "another order and grouping",
            );
            tally.add("orders and groupings compared", 1);
        }
        return;
    }
    panic!("none of {ATTEMPTS} inputs was built without a division by zero");
}

#[test]
fn uniqueness_every_order_and_grouping_of_the_operands_gives_one_term() {
    let tally = run("uniqueness", UNIQUENESS_SEED, uniqueness_case);
    tally.require(
        "uniqueness",
        &[
            "orders and groupings compared",
            "defined points",
            "undefined points",
            "inputs drawn again after a division by zero",
        ],
    );
    tally.require("uniqueness", &SCALED_SUMS);
}

/// Idempotence: every node of a term has the canonical shape, and the term
/// rebuilt through the constructors from the parts that its accessors give,
/// in their stored order and reversed, is the term itself. Moreover, a
/// content that cancels against a coefficient leaves no product: every sum
/// $s$ in the term, with the content $c$, times $1/c$ is its primitive part,
/// a sum over the cores of $s$ with the content 1, and $c$ times that part
/// is $s$ again.
fn idempotence_case(case: &mut Case, tally: &mut Tally) {
    let (_, term, _) = draw(case, tally, input, plain);
    check_shape(&term);
    for reversed in [false, true] {
        let rebuilt = rebuild(&term, reversed, &mut case.context);
        assert_same_term(&term, &rebuilt, &mut case.context, "the rebuilt term");
        tally.add("terms rebuilt", 1);
    }
    for node in nodes(&term) {
        if node.as_sum().is_some() {
            tally.add("sums rebuilt", 1);
            assert_content_cancels(&node, &mut case.context, tally);
        }
    }
}

/// Asserts that a sum $s$ with the content $c$ times $1/c$ is its primitive
/// part, whose content is 1, and that $c$ times that part is $s$ again.
fn assert_content_cancels(sum: &Term, context: &mut Context, tally: &mut Tally) {
    let (constant, coefficients, _) = sum.as_sum().expect("a sum");
    let content = coefficients
        .iter()
        .find(|coefficient| !coefficient.is_zero())
        .unwrap_or(constant)
        .clone();
    let inverse = Term::number(content.inverse(context).unwrap(), context).unwrap();
    let part = Term::product(&[inverse, sum.clone()], context).unwrap();
    assert!(
        is_primitive_part(&part, sum) && content_of(&part).is_one(),
        "1/c times the sum {} with the content c = {content} is {}, not its primitive part",
        render(sum),
        render(&part)
    );
    let scale = Term::number(content.clone(), context).unwrap();
    let back = Term::product(&[part, scale], context).unwrap();
    assert_same_term(sum, &back, context, "c times the primitive part of a sum");
    tally.add(
        if is_one_value(&content) {
            "sums whose content is 1 divided by it"
        } else {
            "sums whose content is not 1 divided by it and scaled back"
        },
        1,
    );
}

#[test]
fn idempotence_rebuilding_a_term_from_its_parts_gives_the_term() {
    let tally = run("idempotence", IDEMPOTENCE_SEED, idempotence_case);
    tally.require(
        "idempotence",
        &[
            "terms rebuilt",
            "sums rebuilt",
            "sums whose content is 1 divided by it",
            "sums whose content is not 1 divided by it and scaled back",
        ],
    );
    tally.require("idempotence", &SCALED_SUMS);
}

/// The order of terms: the keys of the factors of every product, by base in
/// the public order and then a nonnegative exponent first, and the cores of
/// every sum increase strictly, and `negative_bases` is sorted strictly. The
/// public `compare` is the order of the contract, written here, on every
/// pair that this checks and on pairs of three terms and some of their
/// subterms; it is antisymmetric there, and `Equal` exactly for equal
/// structure.
fn order_case(case: &mut Case, tally: &mut Tally) {
    let mut terms = Vec::with_capacity(3);
    for _ in 0..3 {
        let (_, term, _) = draw(case, tally, input, plain);
        terms.push(term);
    }
    for term in &terms {
        for node in nodes(term) {
            if let Some((_, factors)) = node.as_product() {
                for pair in factors.windows(2) {
                    let (base, negative) = key(&pair[0]);
                    let (other_base, other_negative) = key(&pair[1]);
                    let keys = compare(&base, &other_base, &mut case.context)
                        .then(negative.cmp(&other_negative));
                    assert_eq!(
                        keys,
                        Ordering::Less,
                        "the factors {} and {} of {} are not in increasing order of their keys",
                        render(&pair[0]),
                        render(&pair[1]),
                        render(&node)
                    );
                    tally.add("pairs of factors in order", 1);
                }
            }
            if let Some((_, _, cores)) = node.as_sum() {
                for pair in cores.windows(2) {
                    assert_eq!(
                        compare(&pair[0], &pair[1], &mut case.context),
                        Ordering::Less,
                        "the cores {} and {} of {} are not in increasing order",
                        render(&pair[0]),
                        render(&pair[1]),
                        render(&node)
                    );
                    tally.add("pairs of monomials in order", 1);
                }
            }
        }
        let bases = term.negative_bases(&mut case.context).unwrap();
        for pair in bases.windows(2) {
            assert_eq!(
                compare(&pair[0], &pair[1], &mut case.context),
                Ordering::Less,
                "negative_bases of {} is not sorted strictly",
                render(term)
            );
        }
    }
    let mut sample = terms.clone();
    for term in &terms {
        let all = nodes(term);
        for _ in 0..2 {
            sample.push(all[case.random.index(all.len())].clone());
        }
    }
    for left in &sample {
        for right in &sample {
            let forward = compare(left, right, &mut case.context);
            let backward = compare(right, left, &mut case.context);
            assert_eq!(
                backward,
                forward.reverse(),
                "compare is not antisymmetric on {} and {}",
                render(left),
                render(right)
            );
            assert_eq!(
                left.equals(right, &mut case.context).unwrap(),
                forward == Ordering::Equal
            );
            assert_eq!(same(left, right), forward == Ordering::Equal);
            tally.add("pairs compared", 1);
        }
    }
}

#[test]
fn order_of_terms_factors_and_monomials_increase_strictly() {
    let tally = run("order of terms", ORDER_SEED, order_case);
    tally.require(
        "order of terms",
        &[
            "pairs of factors in order",
            "pairs of monomials in order",
            "pairs compared",
        ],
    );
    tally.require("order of terms", &SCALED_SUMS);
}

/// Like terms and coefficients: in every sum no two monomials share a core
/// and no core is a number, in every product no two factors share a base
/// and the sign of their exponents and no factor is a number, and the term,
/// built in a random order and grouping, agrees with the model. Moreover,
/// with the same input built apart in another order as $t'$ and scalars $p$
/// and $q$, neither 0 nor 1: $p t + q t' = (p + q) t$, also when $t$ is a
/// sum, which $p$ and $q$ scale into sums over its cores. Writing a symbol
/// $t$ as $1 \cdot t$ and a sum $t$ as $c \cdot u$, with its content $c$ and
/// its primitive part $u$: a sum times a symbol $z$ is $c \cdot z \cdot u$,
/// and $t^a t'^b$ is $c^{a + b}$ times $u^{a + b}$ when $a$ and $b$ have one
/// sign, and times the two factors $u^a$ and $u^b$ otherwise.
fn merging_case(case: &mut Case, tally: &mut Tally) {
    let (input, term, points) = draw(case, tally, input, realize);
    for node in nodes(&term) {
        if let Some((_, _, cores)) = node.as_sum() {
            for (index, core) in cores.iter().enumerate() {
                assert!(
                    core.as_number().is_none(),
                    "the sum {} has a number among its cores",
                    render(&node)
                );
                for other in &cores[index + 1..] {
                    assert!(
                        !same(core, other),
                        "two monomials of {} have the core {}",
                        render(&node),
                        render(core)
                    );
                }
            }
            tally.add("sums checked", 1);
        }
        if let Some((_, factors)) = node.as_product() {
            for (index, factor) in factors.iter().enumerate() {
                assert!(
                    factor.as_number().is_none(),
                    "the product {} has a number among its factors",
                    render(&node)
                );
                let (base, negative) = key(factor);
                for other in &factors[index + 1..] {
                    let (other_base, other_negative) = key(other);
                    assert!(
                        negative != other_negative || !same(&base, &other_base),
                        "two factors of {} have the base {} and one sign of exponent",
                        render(&node),
                        render(&base)
                    );
                }
            }
            tally.add("products checked", 1);
        }
    }
    agree(&input, &term, &points, tally);

    let context = &mut case.context;
    let copy = realize(&input, &mut case.random, context, tally).unwrap();
    let (p, q) = (case.random.pick(&SCALES), case.random.pick(&SCALES));
    let (p_value, q_value) = (Fraction::new(p.0, p.1), Fraction::new(q.0, q.1));
    let p = Rational::new(Integer::from(p.0), Integer::from(p.1), context).unwrap();
    let q = Rational::new(Integer::from(q.0), Integer::from(q.1), context).unwrap();
    let p_plus_q = Term::number(p.add(&q, context).unwrap(), context).unwrap();
    let p = Term::number(p, context).unwrap();
    let q = Term::number(q, context).unwrap();
    let left = Term::product(&[p, term.clone()], context).unwrap();
    let right = Term::product(&[copy.clone(), q], context).unwrap();
    if term.as_sum().is_some() {
        assert_scaled(&left, &term, &p_value, "p t");
        assert_scaled(&right, &copy, &q_value, "t' q");
        tally.add("sums scaled by p and q", 1);
    }
    let merged = Term::sum(&[left, right], context).unwrap();
    let expected = Term::product(&[p_plus_q, term.clone()], context).unwrap();
    assert_same_term(&merged, &expected, context, "p t + q t'");
    tally.add("like monomials merged", 1);
    if term.as_sum().is_some() {
        tally.add("like monomials of sums merged", 1);
    }

    if term.as_sum().is_some() {
        let symbol = Term::symbol(NAMES[case.random.index(NAMES.len())], context).unwrap();
        let product = Term::product(&[term.clone(), symbol.clone()], context).unwrap();
        let kept = product.as_product().is_some_and(|(coefficient, factors)| {
            Fraction::of(coefficient).equals(&content(&term))
                && factors.len() == 2
                && same(&factors[0], &symbol)
                && is_primitive_part(&factors[1], &term)
        });
        assert!(
            kept,
            "the sum {} times the symbol {} gives {}, not its content times the symbol and its primitive part",
            render(&term),
            render(&symbol),
            render(&product)
        );
        tally.add(
            if content(&term).is_one() {
                "sums whose content is 1 times a symbol"
            } else {
                "sums whose content is not 1 times a symbol"
            },
            1,
        );
    }

    if matches!(term.kind(), TermKind::Symbol | TermKind::Sum) {
        let a = case.random.pick(&NONZERO_EXPONENTS);
        let b = case.random.pick(&NONZERO_EXPONENTS);
        let first = term.power(a, context).unwrap();
        let second = copy.power(b, context).unwrap();
        let product = Term::product(&[first, second], context).unwrap();
        let scale = content_of(&term)
            .power(a + b)
            .expect("the content of a sum is not 0");
        if (a > 0) == (b > 0) {
            assert!(
                is_scaled_power(&product, &scale, &term, a + b),
                "the factors of exponents {a} and {b} of {} give {}, not {} times the power {} of its primitive part",
                render(&term),
                render(&product),
                scale.text(),
                a + b
            );
            tally.add("like factors merged", 1);
        } else {
            let (positive, negative) = if a > 0 { (a, b) } else { (b, a) };
            let kept = product.as_product().is_some_and(|(coefficient, factors)| {
                Fraction::of(coefficient).equals(&scale)
                    && factors.len() == 2
                    && (if positive == 1 {
                        is_base_part(&factors[0], &term)
                    } else {
                        is_power_of_part(&factors[0], &term, positive)
                    })
                    && is_power_of_part(&factors[1], &term, negative)
            });
            assert!(
                kept,
                "the factors of exponents {a} and {b} of {} give {}, not {} times the two powers of its primitive part",
                render(&term),
                render(&product),
                scale.text()
            );
            tally.add("factors of opposite signs kept apart", 1);
        }
        if term.as_sum().is_some() && !content(&term).is_one() {
            tally.add("like factors of sums whose content is not 1", 1);
        }
    }
}

#[test]
fn merging_leaves_no_like_terms_and_keeps_the_value() {
    let tally = run("like terms and coefficients", MERGING_SEED, merging_case);
    tally.require(
        "like terms and coefficients",
        &[
            "sums checked",
            "products checked",
            "defined points",
            "undefined points",
            "like monomials merged",
            "sums scaled by p and q",
            "like monomials of sums merged",
            "sums whose content is 1 times a symbol",
            "sums whose content is not 1 times a symbol",
            "like factors merged",
            "factors of opposite signs kept apart",
            "like factors of sums whose content is not 1",
        ],
    );
    tally.require("like terms and coefficients", &SCALED_SUMS);
}

/// The elimination of 0 and 1: no node keeps a 0 or a 1 but a witness, as
/// [`check_eliminated`] states; $t + 0$, $0 + t$, $t \cdot 1$, $1 \cdot t$,
/// $t^1$ and the sum and the product of $t$ alone are $t$; the empty sum is
/// 0 and the empty product 1; $0 \cdot t$ and $t \cdot 0$ are 0 or the zero
/// witness of $\max N(t)$, and $t^0$ is 1 or the ones of $\max N(t)$. A
/// number distributes over a sum, so the negation of a sum $t$ is the sum
/// with the negated constant and coefficients, and the monomials of $t - t$
/// and of $t - t'$, with the same input built apart in another order and
/// grouping as $t'$, cancel to 0 or to the zero witness of $\max N(t)$ for
/// every $t$, a sum or not; their power $-1$, and the quotient of $t$ by
/// them, fail with `DivisionByZero`.
fn elimination_case(case: &mut Case, tally: &mut Tally) {
    let (input, term, _) = draw(case, tally, input, plain);
    let context = &mut case.context;
    check_eliminated(&term);
    let zero = number(0, 1, context).unwrap();
    let one = number(1, 1, context).unwrap();
    let identities = [
        ("t + 0", Term::sum(&[term.clone(), zero.clone()], context)),
        ("0 + t", Term::sum(&[zero.clone(), term.clone()], context)),
        (
            "the sum of t alone",
            Term::sum(std::slice::from_ref(&term), context),
        ),
        (
            "t * 1",
            Term::product(&[term.clone(), one.clone()], context),
        ),
        ("1 * t", Term::product(&[one, term.clone()], context)),
        (
            "the product of t alone",
            Term::product(std::slice::from_ref(&term), context),
        ),
        ("t^1", term.power(1, context)),
    ];
    for (what, result) in identities {
        assert_same_term(&term, &result.unwrap(), context, what);
        tally.add("identities of 0 and 1", 1);
    }
    let empty_sum = Term::sum(&[], context).unwrap();
    assert!(empty_sum.as_number().is_some_and(Rational::is_zero));
    let empty_product = Term::product(&[], context).unwrap();
    assert!(empty_product.as_number().is_some_and(is_one_value));

    let bases = maximal(&negative_set(&term));
    tally.add(
        if bases.is_empty() {
            "terms without negative bases"
        } else {
            "terms with negative bases"
        },
        1,
    );
    let mut results = Vec::new();
    let left = Term::product(&[zero.clone(), term.clone()], context).unwrap();
    assert_zero_witness(&left, &bases, "0 * t");
    results.push(left);
    let right = Term::product(&[term.clone(), zero], context).unwrap();
    assert_zero_witness(&right, &bases, "t * 0");
    results.push(right);
    let power = term.power(0, context).unwrap();
    assert_ones(&power, &bases, "t^0");
    results.push(power);
    let negation = term.negate(context).unwrap();
    if term.as_sum().is_some() {
        assert_scaled(&negation, &term, &Fraction::new(-1, 1), "-t");
        tally.add("negations of sums", 1);
    }
    let copy = realize(&input, &mut case.random, context, tally).unwrap();
    let differences = [
        ("t - t", term.subtract(&term, context)),
        ("t - t'", term.subtract(&copy, context)),
    ];
    for (what, difference) in differences {
        let difference = difference.unwrap();
        assert_zero_witness(&difference, &bases, what);
        for (operation, reciprocal) in [
            ("the power -1", difference.power(-1, context)),
            ("the quotient of t", term.divide(&difference, context)),
        ] {
            match reciprocal {
                Err(error) => assert_division_by_zero(&error),
                Ok(result) => panic!(
                    "{operation} of {what} = {} is {}, not a division by zero",
                    render(&difference),
                    render(&result)
                ),
            }
        }
        results.push(difference);
    }
    tally.add("differences t - t", 1);
    if term.as_sum().is_some() {
        tally.add("differences t - t of sums", 1);
    }
    for result in &results {
        check_eliminated(result);
    }
}

#[test]
fn elimination_no_zero_and_no_one_is_left_but_a_witness() {
    let tally = run("elimination of 0 and 1", ELIMINATION_SEED, elimination_case);
    tally.require(
        "elimination of 0 and 1",
        &[
            "identities of 0 and 1",
            "terms without negative bases",
            "terms with negative bases",
            "negations of sums",
            "differences t - t",
            "differences t - t of sums",
        ],
    );
    tally.require("elimination of 0 and 1", &SCALED_SUMS);
}

/// Integer powers: the power of a base follows the rules of powers, worked
/// out here from the structure of the base: a number strictly, the exponent
/// 1 and 0, the distribution over a product with $c^k$ computed strictly, a
/// sum $s = c \cdot p$ with its content $c$ and its primitive part $p$ as
/// $c^k p^k$, which is $p^k$ alone when $c^k = 1$, as in
/// $(1 - x)^2 = (x - 1)^2$, and the merge condition of a power of a power.
/// Every node of the result has the canonical shape, $N$ of the base is
/// contained in $N$ of the result, the result agrees with the model, and
/// every integer power of a one $(b^{-1})^0$ in the base or the result is
/// the one itself.
fn powers_case(case: &mut Case, tally: &mut Tally) {
    for _ in 0..ATTEMPTS {
        let base = power_base(&mut case.random);
        let exponent = case.random.pick(&POWER_EXPONENTS);
        let input = Expression::Power(Box::new(base.clone()), exponent);
        case.note(&input);
        let points = points(&mut case.random);
        let base_term = match build(&base, &mut case.context, tally) {
            Ok(term) => term,
            Err(error) => {
                assert_division_by_zero(&error);
                assert_undefined(&base, &points);
                case.drawn_again(tally);
                continue;
            }
        };
        check_shape(&base_term);
        count_scaled_base(&base_term, exponent, tally);
        let expected = expected_power(&base_term, exponent, &mut case.context, tally);
        let what = format!("{} to the power {exponent}", render(&base_term));
        let result = match (base_term.power(exponent, &mut case.context), expected) {
            (Err(error), Expected::DivisionByZero) => {
                assert_division_by_zero(&error);
                assert_undefined(&input, &points);
                tally.add("strict divisions by zero", 1);
                return;
            }
            (Err(error), _) => panic!("{what} failed: {error}"),
            (Ok(result), expected) => {
                assert_expected(&result, &expected, &what);
                result
            }
        };
        tally.add("nodes of the terms", result.size());
        check_shape(&result);
        assert_keeps_negative_bases(std::slice::from_ref(&base_term), &result);
        agree(&input, &result, &points, tally);
        let other = case.random.pick(&POWER_EXPONENTS);
        for one in ones(&base_term).into_iter().chain(ones(&result)) {
            for power in [exponent, other] {
                let raised = one.power(power, &mut case.context).unwrap();
                assert!(
                    same(&raised, &one),
                    "the one {} to the power {power} is {}",
                    render(&one),
                    render(&raised)
                );
                tally.add("powers of ones", 1);
            }
        }
        return;
    }
    panic!("none of {ATTEMPTS} bases was built without a division by zero");
}

#[test]
fn integer_powers_merge_distribute_and_keep_their_values() {
    let tally = run("integer powers", POWERS_SEED, powers_case);
    tally.require(
        "integer powers",
        &[
            "numeric bases",
            "exponent 1",
            "exponent 0 giving 1",
            "exponent 0 giving ones",
            "powers of products",
            "negative powers of products with the coefficient 0",
            "strict divisions by zero",
            "powers of sums whose content is 1",
            "powers of sums with a scaled power of the content",
            "powers of sums whose content is not 1 but whose power is 1",
            "merged powers of powers",
            "powers of powers kept apart",
            "powers of ones",
            "defined points",
            "undefined points",
        ],
    );
    tally.require("integer powers", &SCALED_SUMS);
}

/// The negative-exponent invariant: for a sum, a product, a power, a
/// negation, a difference or a quotient whose operands are often one of the
/// shapes $x^2 \cdot x^{-1}$, $x \cdot x^{-1}$, $0 \cdot x^{-1}$ and
/// $(x^{-1})^0$ on a random base, $N$ of each operand is contained in $N$ of
/// the result, and so at every constructor of the generator tree, with $N$
/// computed here on each canonical term and its sums compared by their
/// primitive parts. Read on the generator tree itself, every base of a
/// negative power and every divisor of the input whose canonical form is a
/// symbol, or a sum by its primitive part, is in $N$ of the result, so
/// $(2x + 2y)^{-1}$ keeps $x + y$; a base of another kind is not kept as
/// written, since a power distributes over a product,
/// $(2x)^{-1} = \frac{1}{2} x^{-1}$, and merges with a power,
/// $(x^2)^{-1} = x^{-2}$. `negative_bases` and `has_negative_power` agree
/// with $N$, a shape on a symbol is kept as written and a shape on a sum by
/// its content and its primitive part, and wherever the input is undefined
/// the result is too.
fn negative_bases_case(case: &mut Case, tally: &mut Tally) {
    for _ in 0..ATTEMPTS {
        let (input, shapes) = negative_bases_input(&mut case.random);
        case.note(&input);
        let points = points(&mut case.random);
        let (operands, result) = match construct(&input, &mut case.context, tally) {
            Ok(built) => built,
            Err(error) => {
                assert_division_by_zero(&error);
                assert_undefined(&input, &points);
                case.drawn_again(tally);
                continue;
            }
        };
        assert_keeps_negative_bases(&operands, &result);
        tally.add(constructor_name(&input), 1);
        tally.add("nodes of the terms", result.size());
        assert_negative_bases(&result, &mut case.context);
        for operand in &operands {
            assert_negative_bases(operand, &mut case.context);
        }
        agree(&input, &result, &points, tally);
        let kept = negative_set(&result);
        let mut bases = Vec::new();
        written_negative_bases(&input, &mut bases);
        for base in bases {
            let base = build(base, &mut case.context, tally).unwrap();
            if matches!(base.kind(), TermKind::Symbol | TermKind::Sum) {
                assert!(
                    contains(&kept, &base),
                    "the base {} of a negative power of the input, by its primitive part, is not in N of the result {}",
                    render(&base),
                    render(&result)
                );
                tally.add("negative bases of the generator tree kept", 1);
                if !content_of(&base).is_one() {
                    tally.add(
                        "negative bases of the generator tree that are sums whose content is not 1",
                        1,
                    );
                }
            }
        }
        for (position, shape, base) in &shapes {
            let base = build(base, &mut case.context, tally).unwrap();
            if matches!(base.kind(), TermKind::Symbol | TermKind::Sum) {
                assert_kept_as_written(&operands[*position], *shape, &base);
                tally.add("shapes kept as written", 1);
                if !content_of(&base).is_one() {
                    tally.add("shapes on sums whose content is not 1", 1);
                }
            }
        }
        count_shapes(&input, tally);
        if !negative_set(&result).is_empty() {
            tally.add("results with negative bases", 1);
        }
        return;
    }
    panic!("none of {ATTEMPTS} inputs was built without a division by zero");
}

#[test]
fn negative_exponents_every_constructor_keeps_the_negative_bases_of_its_operands() {
    let tally = run(
        "negative exponents",
        NEGATIVE_BASES_SEED,
        negative_bases_case,
    );
    tally.require(
        "negative exponents",
        &[
            "sum",
            "product",
            "power",
            "negation",
            "difference",
            "quotient",
            "shapes kept as written",
            "shapes on sums whose content is not 1",
            "negative bases of the generator tree kept",
            "negative bases of the generator tree that are sums whose content is not 1",
            "results with negative bases",
            "defined points",
            "undefined points",
            "inputs drawn again after a division by zero",
        ],
    );
    tally.require("negative exponents", &SCALED_SUMS);
    for shape in SHAPES {
        let count = tally.get(shape.name());
        assert!(
            count >= 100,
            "the generator wrote the {} only {count} times",
            shape.name()
        );
    }
}
