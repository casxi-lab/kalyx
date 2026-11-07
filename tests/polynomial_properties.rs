//! Property tests of the univariate polynomials against a reference written
//! here, from fixed seeds, as testing obligation 5 of
//! `docs/components/polynomials/contract.md` asks. The tests use only the
//! public interface of the library and were written by an author other than
//! the author of the polynomials.
//!
//! Five properties of 1,000 cases each check the arithmetic of
//! $\mathbb{Q}[x]$:
//!
//! - `products_commute`: $p q = q p$;
//! - `products_associate`: $(p q) r = p (q r)$;
//! - `products_distribute_over_sums`: $p (q + r) = p q + p r = (q + r) p$;
//! - `the_derivative_is_linear`: $(a p + b q)' = a p' + b q'$ for rationals
//!   $a$ and $b$;
//! - `the_derivative_follows_the_product_rule`: $(p q)' = p' q + p q'$.
//!
//! The sides of each identity and its intermediate results, such as $q + r$
//! or $p'$, are computed by a function that is generic over the coefficient
//! rings for which the contract states the operations of `PolynomialRing`,
//! `K: CoefficientRing<Undecided = Infallible>`, with no other bound on the
//! elements, and that the tests instantiate with `Rationals`. Functions
//! generic over the same bound compare the sides with each other through the
//! coefficient ring, by `subtract` and `zero_test`, never by `==` on the
//! coefficients, and check the canonical form of every result: as many
//! coefficients as degrees, the degrees strictly increasing, no coefficient
//! that the zero test finds zero, `degree` the last degree, and `is_zero`
//! exactly for no term. Every side and every intermediate result is also
//! compared, term by term, with the result of the reference.
//!
//! `powers_of_x_plus_1_have_the_binomial_coefficients` builds $(x + 1)^n$ for
//! $n = 0, \dots, 224$, 225 cases, twice each: by `power` of the ring,
//! through a function generic over the same bounds, and by the expansion of
//! the parsed term `(x + 1)^n`. Both must have the $n + 1$ terms of degrees 0
//! to $n$, the coefficient of $x^k$ being $\binom{n}{k}$, which the test
//! computes by Pascal's rule with the integers of the reference and checks
//! against $\sum_k \binom{n}{k} = 2^n$.
//!
//! **The inputs.** The generator writes each input as a list of terms
//! $c x^d$ in the variable of its case, one of `x`, `t`, `y`, `z_1` and
//! `theta`, in one of these shapes: the zero polynomial, with no term or with
//! two terms that cancel; constants; up to seven terms of degree below 10,
//! some of the same degree and some with the coefficient 0; up to five sparse
//! terms of degree $m B + s$ with $1 \le m \le 3$ and $0 \le s \le 3$, where
//! each case draws $B$ from $2^{20}$ to $2^{40}$, so that the degrees of
//! products meet, with or without a constant term; and mixtures of low and
//! sparse terms. The coefficients are $\pm 1$, small integers, small
//! fractions, integers of 20 to 45 digits, and fractions whose denominators
//! $2^a 3^b 5^c 7^d$ may exceed 64 bits, of both signs. Each input is built
//! in one of two ways: by the operations of the ring, as the sum of the
//! products of `constant(c)` and `power(x, d)` in the order of the list,
//! each joined to the total by `add` from either side or by `subtract` of its
//! `negate`; or by the expansion of the sum of the terms, built with the
//! constructors of the term core, which merge the terms of the same degree
//! first. Half of the sums that are expanded have one more summand whose
//! value is 0, $c \, ((x + 1)^2 - x^2 - 2 x - 1)^k$ with $1 \le k \le 3$. The
//! term core keeps the inner sum: for $k = 1$ it merges the scaled sum into
//! the sum of the input, and for $k \ge 2$ the power is the core of a
//! monomial that expands to the zero polynomial, which the expansion adds
//! after the constant of the sum, to a total other than zero when the input
//! has a constant term. Either way, the input is checked against the
//! reference before it is used. Some cases relate their inputs, so that
//! coefficients cancel in the operations: $q = p$; conjugates $p = A + B$ and
//! $q = A - B$, whose product is $A^2 - B^2$; $r = -q$ and $r = s - q$ in
//! $q + r$; $r$ the conjugate of $p$ in $(p q) r$; and $q = p$ with $b = -a$,
//! or $a = 0$ or $b = 0$, in $a p + b q$. Counters name what the cases
//! exercised, and each property asserts that its cases exercised zero and
//! constant inputs, sparse high degrees, negative and fractional
//! coefficients, coefficients beyond 64 bits, coefficients that cancel in the
//! operations of the reference, zero results, both ways of building an input
//! and the summands whose value is 0.
//!
//! **The reference.** A polynomial of the reference is an ordered map from
//! the degree to a coefficient that is not zero, with its own sum, product
//! and derivative. Its coefficients are fractions of integers of any size
//! written here, a sign and 32-bit limbs, with their own addition,
//! multiplication, exact division by a small prime and decimal text. A
//! fraction divides out the common factors 2, 3, 5 and 7, the only prime
//! factors of the denominators of the generator, and two fractions are equal
//! when their cross products are. The reference calls nothing of the library:
//! the numbers of the library enter it only through their decimal text, and
//! the coefficients of the inputs reach the library from the decimal text of
//! the reference through `Rational::parse_decimal`, `negate` and `divide`.
//! `the_reference_agrees_with_values_computed_by_hand` checks the reference
//! itself.
//!
//! Each case draws from its own seed, the next output of a SplitMix64
//! started at the fixed seed of its property, and builds its ring and its
//! inputs in a fresh context whose limits are far above every case; no amount
//! of work is asserted. A failing case prints its index, its seed and its
//! inputs, and
//! `check(&mut Case::new(property, index, seed), &mut Tally::default())`,
//! with the case function of the property as `check`, runs it alone.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "a failed check panics, and the guard of its case prints the seed and the inputs"
)]

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::convert::Infallible;

use kalyx::coefficient::{CoefficientRing, Rationals, ZeroTest};
use kalyx::context::CancelFlag;
use kalyx::number::Rational;
use kalyx::polynomial::{Polynomial, PolynomialRing};
use kalyx::term::Term;
use kalyx::{Context, Limits, parse};

/// The cases of each property.
const CASES: u64 = 1_000;

/// The binomial powers $(x + 1)^n$, for $n = 0, \dots, 224$.
const BINOMIAL_POWERS: u64 = 225;

const COMMUTATIVITY_SEED: u64 = 0x504F_4C59_0000_0001;
const ASSOCIATIVITY_SEED: u64 = 0x504F_4C59_0000_0002;
const DISTRIBUTIVITY_SEED: u64 = 0x504F_4C59_0000_0003;
const LINEARITY_SEED: u64 = 0x504F_4C59_0000_0004;
const PRODUCT_RULE_SEED: u64 = 0x504F_4C59_0000_0005;

/// The variables of the rings of the cases; none is a reserved name.
const VARIABLES: [&str; 5] = ["x", "t", "y", "z_1", "theta"];

/// The denominators of the small fractions of the generator.
const DENOMINATORS: [u64; 10] = [2, 3, 4, 5, 6, 7, 8, 9, 10, 12];

/// The primes that a fraction of the reference divides out: every
/// denominator of the generator, and so of every result, is a product of
/// them.
const SMALL_PRIMES: [u32; 4] = [2, 3, 5, 7];

/// The lowest step $B$ of the sparse degrees $m B + s$; the highest is
/// [`SPARSE_STEP_MAX`].
const SPARSE_STEP_MIN: u64 = 1 << 20;

/// The highest step $B$ of the sparse degrees.
const SPARSE_STEP_MAX: u64 = 1 << 40;

/// The shapes of the inputs, drawn with these weights.
const SHAPES: [Shape; 12] = [
    Shape::Zero,
    Shape::Constant,
    Shape::Constant,
    Shape::Low,
    Shape::Low,
    Shape::Low,
    Shape::Low,
    Shape::Sparse,
    Shape::Sparse,
    Shape::Sparse,
    Shape::Mixed,
    Shape::Mixed,
];

/// The ways in which the operations of the ring join a term to the total.
const JOINS: [Join; 3] = [Join::Add, Join::AddToTheLeft, Join::SubtractTheNegation];

/// The counters that every property requires to be exercised.
const REQUIRED: [&str; 11] = [
    "zero inputs",
    "constant inputs",
    "inputs of sparse high degree",
    "inputs with negative coefficients",
    "inputs with fractional coefficients",
    "inputs with coefficients beyond 64 bits",
    "coefficients that cancelled in the operations of the reference",
    "zero results",
    "inputs built by the operations",
    "inputs built by expansion",
    "inputs expanded with a summand whose value is 0",
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

    /// A value in `0..bound`, for a `bound` above 0.
    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    /// A value in `low..=high`, for `low` at most `high` and below
    /// `u64::MAX`.
    fn between(&mut self, low: u64, high: u64) -> u64 {
        low + self.below(high - low + 1)
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

    /// A decimal integer of `digits` digits, the first of them not 0.
    fn digits(&mut self, digits: u64) -> String {
        let mut text = String::new();
        for position in 0..digits {
            let digit = if position == 0 {
                self.between(1, 9)
            } else {
                self.below(10)
            };
            text.push_str(&digit.to_string());
        }
        text
    }
}

/// One case of a property: its seed, its random source, its context and the
/// inputs that it drew. A case that panics prints its seed and its inputs
/// when it is dropped.
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

    /// Draws the variable of the case and builds its ring.
    fn ring(&mut self) -> PolynomialRing {
        let variable = self.random.pick(&VARIABLES);
        self.inputs.push(format!("variable: {variable}"));
        PolynomialRing::new(Rationals, variable, &mut self.context)
            .expect("the ring of a variable that is a symbol name")
    }

    /// Draws the step $B$ of the sparse degrees of the case.
    fn step(&mut self) -> u64 {
        self.random.between(SPARSE_STEP_MIN, SPARSE_STEP_MAX)
    }

    /// An input of a shape drawn at random.
    fn input(&mut self, step: u64) -> Input {
        let terms = terms(&mut self.random, step);
        self.input_of(terms)
    }

    /// An input of `terms`, with the way to build it drawn at random.
    fn input_of(&mut self, mut terms: Vec<(u64, Fraction)>) -> Input {
        self.random.shuffle(&mut terms);
        let path = if self.random.chance(1, 3) {
            let vanishing = if self.random.chance(1, 2) {
                let exponent = self.random.between(1, 3) as i64;
                Some((coefficient(&mut self.random), exponent))
            } else {
                None
            };
            Path::Expansion(vanishing)
        } else {
            let mut joins = Vec::with_capacity(terms.len());
            for _ in 0..terms.len() {
                joins.push(self.random.pick(&JOINS));
            }
            Path::Operations(joins)
        };
        Input { terms, path }
    }

    /// The conjugates $A + B$ and $A - B$ of two inputs $A$ and $B$ drawn at
    /// random, whose product is $A^2 - B^2$.
    fn conjugates(&mut self, step: u64, tally: &mut Tally) -> (Input, Input) {
        let common = terms(&mut self.random, step);
        let differing = terms(&mut self.random, step);
        let mut sum = common.clone();
        sum.extend(differing.iter().cloned());
        let mut difference = common;
        difference.extend(negated_terms(&differing));
        tally.add("conjugate inputs", 1);
        (self.input_of(sum), self.input_of(difference))
    }

    /// A rational scalar of the case: 0 with the probability
    /// `zero_numerator / zero_denominator`, otherwise a coefficient of the
    /// generator.
    fn scalar(&mut self, name: &str, zero_numerator: u64, zero_denominator: u64) -> Fraction {
        let value = if self.random.chance(zero_numerator, zero_denominator) {
            Fraction::integer(Big::from_u64(0))
        } else {
            coefficient(&mut self.random)
        };
        self.inputs.push(format!("{name} = {}", value.text()));
        value
    }

    /// Builds `input` in `ring` in its way, checks the polynomial against the
    /// reference and returns both.
    fn build(
        &mut self,
        name: &str,
        ring: &PolynomialRing,
        input: &Input,
        tally: &mut Tally,
    ) -> (Polynomial, Model) {
        self.inputs
            .push(format!("{name} = {}", input.text(ring.variable())));
        let model = Model::of_terms(&input.terms, tally);
        count_input(&model, tally);
        let built = match &input.path {
            Path::Operations(joins) => {
                tally.add("inputs built by the operations", 1);
                let mut terms = Vec::with_capacity(input.terms.len());
                for ((degree, coefficient), join) in input.terms.iter().zip(joins) {
                    let element = rational(coefficient, &mut self.context);
                    terms.push((*degree, element, *join));
                }
                by_operations(ring, &terms, &mut self.context)
            }
            Path::Expansion(vanishing) => {
                tally.add("inputs built by expansion", 1);
                if vanishing.is_some() {
                    tally.add("inputs expanded with a summand whose value is 0", 1);
                }
                by_expansion(ring, &input.terms, vanishing.as_ref(), &mut self.context)
            }
        };
        let polynomial = built.unwrap_or_else(|error| panic!("{name} was not built: {error:?}"));
        assert_polynomial(name, ring, &polynomial, &model, &mut self.context);
        (polynomial, model)
    }

    /// Checks the results of a property: the sides agree with each other
    /// through the coefficient ring, and every side has the terms of
    /// `expected` and every intermediate result those of its model in
    /// `steps`, in the same order.
    fn verify(
        &mut self,
        ring: &PolynomialRing,
        results: &Results<Rationals>,
        expected: &Model,
        steps: &[(&str, Model)],
        tally: &mut Tally,
    ) {
        let agreed = agree(ring, &results.sides, &mut self.context)
            .expect("the comparison through the coefficient ring");
        let names: Vec<&str> = results.sides.iter().map(|side| side.0).collect();
        assert!(
            agreed,
            "the sides {names:?} differ through the coefficient ring"
        );
        for (name, side) in &results.sides {
            assert_polynomial(name, ring, side, expected, &mut self.context);
        }
        assert_eq!(
            results.steps.len(),
            steps.len(),
            "the intermediate results and their models"
        );
        for ((name, step), (model_name, model)) in results.steps.iter().zip(steps) {
            assert_eq!(name, model_name, "the intermediate results in their order");
            assert_polynomial(name, ring, step, model, &mut self.context);
        }
        if expected.is_zero() {
            tally.add("zero results", 1);
        }
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
/// the arithmetic, not the limits, and no amount of work is asserted.
fn context() -> Context {
    Context::new(
        Limits::new()
            .with_max_work(u64::MAX)
            .with_max_output_bytes(u64::MAX)
            .with_max_input_bytes(1 << 20)
            .with_max_depth(1 << 12)
            .with_max_nodes(1 << 32)
            .with_max_storage_bytes(1 << 40)
            .with_max_integer_bits(1 << 16)
            .with_max_exponent(1 << 50),
        CancelFlag::new(),
    )
}

// ---------------------------------------------------------------------------
// The integers and fractions of the reference

/// An integer of any size for the reference: a sign and a magnitude in limbs
/// of 32 bits, the least significant first, with no zero limb at the top.
/// Zero has no limbs and is not negative, so equal integers are equal values.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Big {
    negative: bool,
    limbs: Vec<u32>,
}

/// $10^9$, the base of the decimal text of a [`Big`].
const BILLION: u32 = 1_000_000_000;

impl Big {
    fn new(negative: bool, mut limbs: Vec<u32>) -> Self {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        let negative = negative && !limbs.is_empty();
        Self { negative, limbs }
    }

    fn from_u64(value: u64) -> Self {
        Self::new(false, vec![low_limb(value), low_limb(value >> 32)])
    }

    fn from_i64(value: i64) -> Self {
        Self::new(value < 0, Self::from_u64(value.unsigned_abs()).limbs)
    }

    /// The integer of a decimal text with an optional leading `-`.
    fn parse(text: &str) -> Self {
        let (negative, digits) = match text.strip_prefix('-') {
            Some(digits) => (true, digits),
            None => (false, text),
        };
        assert!(!digits.is_empty(), "not a decimal integer: {text:?}");
        let mut limbs: Vec<u32> = Vec::new();
        for digit in digits.bytes() {
            assert!(digit.is_ascii_digit(), "not a decimal integer: {text:?}");
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

    /// The bit length of the magnitude: 0 for zero.
    fn bits(&self) -> u64 {
        match self.limbs.last() {
            Some(top) => (self.limbs.len() as u64 - 1) * 32 + u64::from(32 - top.leading_zeros()),
            None => 0,
        }
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
        if magnitude_at_least(&self.limbs, &other.limbs) {
            Self::new(
                self.negative,
                subtract_magnitudes(&self.limbs, &other.limbs),
            )
        } else {
            Self::new(
                other.negative,
                subtract_magnitudes(&other.limbs, &self.limbs),
            )
        }
    }

    fn times(&self, other: &Self) -> Self {
        Self::new(
            self.negative != other.negative,
            multiply_magnitudes(&self.limbs, &other.limbs),
        )
    }

    /// The quotient by `divisor` when `divisor` divides the integer, else
    /// `None`.
    fn exact_quotient(&self, divisor: u32) -> Option<Self> {
        let (quotient, remainder) = divide_magnitude(&self.limbs, divisor);
        if remainder == 0 {
            Some(Self::new(self.negative, quotient))
        } else {
            None
        }
    }

    /// The decimal text, with a leading `-` when negative.
    fn decimal(&self) -> String {
        // Digits in base $10^9$, the least significant first.
        let mut chunks = Vec::new();
        let mut rest = self.limbs.clone();
        while !rest.is_empty() {
            let (quotient, remainder) = divide_magnitude(&rest, BILLION);
            chunks.push(remainder);
            rest = Self::new(false, quotient).limbs;
        }
        let mut text = String::from(if self.negative { "-" } else { "" });
        match chunks.pop() {
            Some(first) => text.push_str(&first.to_string()),
            None => text.push('0'),
        }
        while let Some(chunk) = chunks.pop() {
            text.push_str(&format!("{chunk:09}"));
        }
        text
    }
}

/// The low 32 bits of `value`.
fn low_limb(value: u64) -> u32 {
    (value & 0xFFFF_FFFF) as u32
}

/// Whether the magnitude `left` is at least the magnitude `right`; neither
/// has a zero limb at the top.
fn magnitude_at_least(left: &[u32], right: &[u32]) -> bool {
    if left.len() != right.len() {
        return left.len() > right.len();
    }
    for (a, b) in left.iter().zip(right).rev() {
        if a != b {
            return a > b;
        }
    }
    true
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
        let other = short.get(index).map_or(0, |limb| u64::from(*limb));
        let value = u64::from(*limb) + other + carry;
        sum.push(low_limb(value));
        carry = value >> 32;
    }
    sum.push(low_limb(carry));
    sum
}

/// `left - right`, for `left` at least `right`.
fn subtract_magnitudes(left: &[u32], right: &[u32]) -> Vec<u32> {
    let mut difference = Vec::with_capacity(left.len());
    let mut borrow = 0_u64;
    for (index, limb) in left.iter().enumerate() {
        let subtrahend = right.get(index).map_or(0, |limb| u64::from(*limb)) + borrow;
        let minuend = u64::from(*limb);
        if minuend >= subtrahend {
            difference.push(low_limb(minuend - subtrahend));
            borrow = 0;
        } else {
            difference.push(low_limb(minuend + (1 << 32) - subtrahend));
            borrow = 1;
        }
    }
    assert_eq!(borrow, 0, "the minuend is at least the subtrahend");
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

/// The quotient and the remainder of a magnitude by a nonzero `divisor`.
fn divide_magnitude(limbs: &[u32], divisor: u32) -> (Vec<u32>, u32) {
    assert_ne!(divisor, 0, "a division by zero in the reference");
    let divisor = u64::from(divisor);
    let mut quotient = vec![0_u32; limbs.len()];
    let mut remainder = 0_u64;
    for (limb, digit) in limbs.iter().zip(quotient.iter_mut()).rev() {
        let value = (remainder << 32) | u64::from(*limb);
        *digit = low_limb(value / divisor);
        remainder = value % divisor;
    }
    (quotient, low_limb(remainder))
}

/// An exact rational of the reference: a numerator over a positive
/// denominator, with the common factors 2, 3, 5 and 7 divided out. Two
/// fractions are equal when their cross products are.
#[derive(Clone, Debug)]
struct Fraction {
    numerator: Big,
    denominator: Big,
}

impl Fraction {
    fn new(mut numerator: Big, mut denominator: Big) -> Self {
        assert!(
            !denominator.is_zero() && !denominator.negative,
            "the denominators of the reference are positive"
        );
        if numerator.is_zero() {
            return Self::integer(numerator);
        }
        for prime in SMALL_PRIMES {
            while let (Some(n), Some(d)) = (
                numerator.exact_quotient(prime),
                denominator.exact_quotient(prime),
            ) {
                numerator = n;
                denominator = d;
            }
        }
        Self {
            numerator,
            denominator,
        }
    }

    fn integer(value: Big) -> Self {
        Self {
            numerator: value,
            denominator: Big::from_u64(1),
        }
    }

    fn small(numerator: i64, denominator: u64) -> Self {
        Self::new(Big::from_i64(numerator), Big::from_u64(denominator))
    }

    /// The value of a rational of the library, read through the decimal text
    /// of its parts.
    fn of(value: &Rational) -> Self {
        Self::new(
            Big::parse(&value.numerator().to_string()),
            Big::parse(&value.denominator().to_string()),
        )
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    fn is_negative(&self) -> bool {
        self.numerator.negative
    }

    /// Whether the fraction is an integer; its denominator is a product of
    /// the small primes, which it shares with no numerator, so it is 1
    /// exactly for an integer.
    fn is_integer(&self) -> bool {
        self.denominator == Big::from_u64(1)
    }

    /// The larger bit length of the parts.
    fn bits(&self) -> u64 {
        self.numerator.bits().max(self.denominator.bits())
    }

    fn negated(&self) -> Self {
        Self {
            numerator: self.numerator.negated(),
            denominator: self.denominator.clone(),
        }
    }

    fn plus(&self, other: &Self) -> Self {
        if self.denominator == other.denominator {
            return Self::new(
                self.numerator.plus(&other.numerator),
                self.denominator.clone(),
            );
        }
        Self::new(
            self.numerator
                .times(&other.denominator)
                .plus(&other.numerator.times(&self.denominator)),
            self.denominator.times(&other.denominator),
        )
    }

    fn times(&self, other: &Self) -> Self {
        Self::new(
            self.numerator.times(&other.numerator),
            self.denominator.times(&other.denominator),
        )
    }

    fn equals(&self, other: &Self) -> bool {
        self.numerator.times(&other.denominator) == other.numerator.times(&self.denominator)
    }

    fn text(&self) -> String {
        if self.is_integer() {
            self.numerator.decimal()
        } else {
            format!(
                "{}/{}",
                self.numerator.decimal(),
                self.denominator.decimal()
            )
        }
    }
}

// ---------------------------------------------------------------------------
// The polynomials of the reference

/// A polynomial of the reference: its coefficients that are not zero, by
/// degree.
#[derive(Clone, Debug, Default)]
struct Model(BTreeMap<u64, Fraction>);

impl Model {
    /// The polynomial of the terms $c x^d$ of an input, some of which may
    /// have the same degree or the coefficient 0; a degree whose terms
    /// cancel is counted.
    fn of_terms(terms: &[(u64, Fraction)], tally: &mut Tally) -> Self {
        let mut sums = BTreeMap::new();
        for (degree, coefficient) in terms {
            if !coefficient.is_zero() {
                accumulate(&mut sums, *degree, coefficient.clone());
            }
        }
        settle(sums, "coefficients that cancelled in the inputs", tally)
    }

    /// The constant polynomial `value`.
    fn constant(value: &Fraction) -> Self {
        let mut terms = BTreeMap::new();
        if !value.is_zero() {
            terms.insert(0, value.clone());
        }
        Self(terms)
    }

    fn plus(&self, other: &Self, tally: &mut Tally) -> Self {
        let mut sums = self.0.clone();
        for (degree, coefficient) in &other.0 {
            accumulate(&mut sums, *degree, coefficient.clone());
        }
        settle(sums, CANCELLED, tally)
    }

    fn times(&self, other: &Self, tally: &mut Tally) -> Self {
        let mut sums = BTreeMap::new();
        for (left_degree, left) in &self.0 {
            for (right_degree, right) in &other.0 {
                let degree = left_degree
                    .checked_add(*right_degree)
                    .expect("the degrees of the cases are far below u64::MAX");
                accumulate(&mut sums, degree, left.times(right));
            }
        }
        settle(sums, CANCELLED, tally)
    }

    /// The derivative: $c x^d$ becomes $d c x^{d - 1}$, and constants vanish.
    fn derivative(&self) -> Self {
        let mut terms = BTreeMap::new();
        for (degree, coefficient) in &self.0 {
            if *degree > 0 {
                let factor = Fraction::integer(Big::from_u64(*degree));
                terms.insert(degree - 1, coefficient.times(&factor));
            }
        }
        Self(terms)
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn degree(&self) -> Option<u64> {
        self.0.keys().next_back().copied()
    }

    /// Whether the two polynomials have the same degrees with equal
    /// coefficients.
    fn same(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .zip(&other.0)
                .all(|((d, c), (e, f))| d == e && c.equals(f))
    }

    /// The terms in increasing degree, as `c*v^d` joined by ` + `.
    fn text(&self, variable: &str) -> String {
        if self.0.is_empty() {
            return String::from("0");
        }
        let terms: Vec<String> = self
            .0
            .iter()
            .map(|(degree, coefficient)| format!("{}*{variable}^{degree}", coefficient.text()))
            .collect();
        terms.join(" + ")
    }
}

/// The counter of the coefficients that cancel in the sums and products of
/// the reference.
const CANCELLED: &str = "coefficients that cancelled in the operations of the reference";

/// Adds `value` to the coefficient of `degree`.
fn accumulate(sums: &mut BTreeMap<u64, Fraction>, degree: u64, value: Fraction) {
    match sums.entry(degree) {
        Entry::Occupied(mut entry) => {
            let sum = entry.get().plus(&value);
            entry.insert(sum);
        }
        Entry::Vacant(entry) => {
            entry.insert(value);
        }
    }
}

/// The polynomial of `sums` without its zero coefficients, each of which is
/// counted under `counter`: every contribution to a sum is not zero, so a
/// zero coefficient is one that cancelled.
fn settle(sums: BTreeMap<u64, Fraction>, counter: &'static str, tally: &mut Tally) -> Model {
    let before = sums.len();
    let terms: BTreeMap<u64, Fraction> = sums
        .into_iter()
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .collect();
    tally.add(counter, (before - terms.len()) as u64);
    Model(terms)
}

/// Counts the shapes of an input.
fn count_input(model: &Model, tally: &mut Tally) {
    match model.degree() {
        None => tally.add("zero inputs", 1),
        Some(0) => tally.add("constant inputs", 1),
        Some(degree) if degree >= SPARSE_STEP_MIN => tally.add("inputs of sparse high degree", 1),
        Some(_) => tally.add("inputs of low degree", 1),
    }
    let coefficients = || model.0.values();
    if coefficients().any(Fraction::is_negative) {
        tally.add("inputs with negative coefficients", 1);
    }
    if coefficients().any(|coefficient| !coefficient.is_integer()) {
        tally.add("inputs with fractional coefficients", 1);
    }
    if coefficients().any(|coefficient| coefficient.bits() > 64) {
        tally.add("inputs with coefficients beyond 64 bits", 1);
    }
}

// ---------------------------------------------------------------------------
// The generator

/// The shape of an input.
#[derive(Clone, Copy, Debug)]
enum Shape {
    /// No term, or two terms that cancel.
    Zero,
    /// One or two terms of degree 0.
    Constant,
    /// One to seven terms of degree below 10.
    Low,
    /// One to five terms of sparse high degree, and maybe a constant.
    Sparse,
    /// Low terms and sparse terms.
    Mixed,
}

/// How the operations of the ring join a term to the total.
#[derive(Clone, Copy, Debug)]
enum Join {
    /// `add(total, term)`.
    Add,
    /// `add(term, total)`.
    AddToTheLeft,
    /// `subtract(total, negate(term))`.
    SubtractTheNegation,
}

/// How an input is built.
enum Path {
    /// By the operations of the ring, each term joined to the total as its
    /// [`Join`] says.
    Operations(Vec<Join>),
    /// By the expansion of the sum of the terms and, when the variant holds
    /// $(c, k)$, the summand $c \, ((x + 1)^2 - x^2 - 2 x - 1)^k$, whose
    /// value is 0.
    Expansion(Option<(Fraction, i64)>),
}

/// An input as the generator writes it: its terms $c x^d$ in the order in
/// which they are built, and how they are built.
struct Input {
    terms: Vec<(u64, Fraction)>,
    path: Path,
}

impl Input {
    fn text(&self, variable: &str) -> String {
        let terms: Vec<String> = self
            .terms
            .iter()
            .map(|(degree, coefficient)| format!("({})*{variable}^{degree}", coefficient.text()))
            .collect();
        let sum = if terms.is_empty() {
            String::from("0")
        } else {
            terms.join(" + ")
        };
        match &self.path {
            Path::Operations(joins) => format!("{sum}, built by the operations {joins:?}"),
            Path::Expansion(None) => format!("{sum}, built by expansion"),
            Path::Expansion(Some((coefficient, exponent))) => format!(
                "{sum} + ({})*(({variable} + 1)^2 - {variable}^2 - 2*{variable} - 1)^{exponent}, \
                 built by expansion",
                coefficient.text()
            ),
        }
    }
}

/// The terms of an input of a shape drawn at random.
fn terms(random: &mut SplitMix64, step: u64) -> Vec<(u64, Fraction)> {
    let mut terms = Vec::new();
    match random.pick(&SHAPES) {
        Shape::Zero => {
            if random.chance(1, 2) {
                let degree = if random.chance(1, 2) {
                    random.below(10)
                } else {
                    sparse_degree(random, step)
                };
                let value = coefficient(random);
                terms.push((degree, value.negated()));
                terms.push((degree, value));
            }
        }
        Shape::Constant => {
            terms.push((0, coefficient(random)));
            if random.chance(1, 4) {
                terms.push((0, coefficient(random)));
            }
        }
        Shape::Low => {
            for _ in 0..random.between(1, 7) {
                let value = if random.chance(1, 12) {
                    Fraction::integer(Big::from_u64(0))
                } else {
                    coefficient(random)
                };
                terms.push((random.below(10), value));
            }
        }
        Shape::Sparse => {
            for _ in 0..random.between(1, 5) {
                terms.push((sparse_degree(random, step), coefficient(random)));
            }
            if random.chance(1, 2) {
                terms.push((0, coefficient(random)));
            }
        }
        Shape::Mixed => {
            for _ in 0..random.between(1, 4) {
                terms.push((random.below(10), coefficient(random)));
            }
            for _ in 0..random.between(1, 3) {
                terms.push((sparse_degree(random, step), coefficient(random)));
            }
        }
    }
    terms
}

/// A sparse degree $m B + s$ with $1 \le m \le 3$ and $0 \le s \le 3$.
fn sparse_degree(random: &mut SplitMix64, step: u64) -> u64 {
    random.between(1, 3) * step + random.below(4)
}

/// The terms with their coefficients negated.
fn negated_terms(terms: &[(u64, Fraction)]) -> Vec<(u64, Fraction)> {
    terms
        .iter()
        .map(|(degree, coefficient)| (*degree, coefficient.negated()))
        .collect()
}

/// A coefficient that is not zero: $\pm 1$, a small integer, a small
/// fraction, an integer of 20 to 45 digits, or a fraction whose denominator
/// $2^a 3^b 5^c 7^d$ may exceed 64 bits.
fn coefficient(random: &mut SplitMix64) -> Fraction {
    let sign = if random.chance(1, 2) { -1 } else { 1 };
    match random.below(12) {
        0..=3 => Fraction::small(sign, 1),
        4..=6 => Fraction::small(sign * random.between(2, 9) as i64, 1),
        7 | 8 => {
            let numerator = sign * random.between(1, 30) as i64;
            Fraction::small(numerator, random.pick(&DENOMINATORS))
        }
        9 => {
            let digits = random.between(20, 45);
            let magnitude = Big::parse(&random.digits(digits));
            Fraction::integer(if sign < 0 {
                magnitude.negated()
            } else {
                magnitude
            })
        }
        _ => {
            let numerator = if random.chance(1, 2) {
                Big::from_i64(sign * random.between(1, 30) as i64)
            } else {
                let digits = random.between(20, 40);
                let magnitude = Big::parse(&random.digits(digits));
                if sign < 0 {
                    magnitude.negated()
                } else {
                    magnitude
                }
            };
            let mut denominator = Big::from_u64(1);
            for (prime, highest) in [(2, 80), (3, 30), (5, 10), (7, 10)] {
                for _ in 0..random.below(highest + 1) {
                    denominator = denominator.times(&Big::from_u64(prime));
                }
            }
            Fraction::new(numerator, denominator)
        }
    }
}

// ---------------------------------------------------------------------------
// Building the inputs in the library

/// The rational of the library with the value of `value`, built from the
/// decimal text of its parts.
fn rational(value: &Fraction, context: &mut Context) -> Rational {
    let magnitude = Rational::parse_decimal(&value.numerator.magnitude().decimal(), context)
        .expect("the magnitude of a numerator");
    let numerator = if value.is_negative() {
        magnitude.negate(context).expect("a negative numerator")
    } else {
        magnitude
    };
    let denominator =
        Rational::parse_decimal(&value.denominator.decimal(), context).expect("a denominator");
    let rational = numerator
        .divide(&denominator, context)
        .expect("a fraction of the generator");
    assert!(
        Fraction::of(&rational).equals(value),
        "the rational {rational} was built for {}",
        value.text()
    );
    rational
}

/// The polynomial of `terms` built by the operations of the ring: the sum of
/// the products of `constant(c)` and `power(x, d)`, each joined to the total
/// as its [`Join`] says, in the order of the list.
fn by_operations<K>(
    ring: &PolynomialRing<K>,
    terms: &[(u64, K::Element, Join)],
    context: &mut Context,
) -> kalyx::Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let x = ring.generator(context)?;
    let mut total = ring.zero(context)?;
    for (degree, coefficient, join) in terms {
        let constant = ring.constant(coefficient, context)?;
        let power = ring.power(&x, *degree, context)?;
        let term = ring.multiply(&constant, &power, context)?;
        total = match join {
            Join::Add => ring.add(&total, &term, context)?,
            Join::AddToTheLeft => ring.add(&term, &total, context)?,
            Join::SubtractTheNegation => {
                let negation = ring.negate(&term, context)?;
                ring.subtract(&total, &negation, context)?
            }
        };
    }
    Ok(total)
}

/// The polynomial of `terms` built by the expansion of their sum, which the
/// constructors of the term core build, with the summand
/// $c \, ((x + 1)^2 - x^2 - 2 x - 1)^k$ last for `vanishing` `Some((c, k))`.
fn by_expansion(
    ring: &PolynomialRing,
    terms: &[(u64, Fraction)],
    vanishing: Option<&(Fraction, i64)>,
    context: &mut Context,
) -> kalyx::Result<Polynomial> {
    let symbol = Term::symbol(ring.variable(), context)?;
    let mut summands = Vec::with_capacity(terms.len() + 1);
    for (degree, coefficient) in terms {
        let number = Term::number(rational(coefficient, context), context)?;
        let exponent = i64::try_from(*degree).expect("the degrees of the generator fit in i64");
        let power = symbol.power(exponent, context)?;
        summands.push(Term::product(&[number, power], context)?);
    }
    if let Some((coefficient, exponent)) = vanishing {
        let number = Term::number(rational(coefficient, context), context)?;
        let zero = vanishing_sum(&symbol, context)?;
        let power = zero.power(*exponent, context)?;
        summands.push(Term::product(&[number, power], context)?);
    }
    let sum = Term::sum(&summands, context)?;
    ring.expand(&sum, context)
}

/// The term $(x + 1)^2 - x^2 - 2 x - 1$ of the symbol $x$, a sum that the
/// term core keeps and whose expansion is the zero polynomial.
fn vanishing_sum(symbol: &Term, context: &mut Context) -> kalyx::Result<Term> {
    let one = Term::number(Rational::from(1_i64), context)?;
    let two = Term::number(Rational::from(2_i64), context)?;
    let shifted = Term::sum(&[symbol.clone(), one.clone()], context)?;
    let square = shifted.power(2, context)?;
    let symbol_squared = symbol.power(2, context)?;
    let twice = Term::product(&[two, symbol.clone()], context)?;
    let sum = Term::sum(
        &[
            square,
            symbol_squared.negate(context)?,
            twice.negate(context)?,
            one.negate(context)?,
        ],
        context,
    )?;
    assert!(
        sum.as_sum().is_some(),
        "the term core keeps the sum (x + 1)^2 - x^2 - 2*x - 1"
    );
    Ok(sum)
}

// ---------------------------------------------------------------------------
// The checks

/// Checks that `polynomial` is in canonical form and has the terms of
/// `model`.
fn assert_polynomial(
    name: &str,
    ring: &PolynomialRing,
    polynomial: &Polynomial,
    model: &Model,
    context: &mut Context,
) {
    let broken =
        canonical_form(ring, polynomial, context).expect("the zero tests of the canonical form");
    if let Some(broken) = broken {
        panic!("{name}: {broken}");
    }
    let mut terms = BTreeMap::new();
    for (degree, coefficient) in polynomial.degrees().iter().zip(polynomial.coefficients()) {
        terms.insert(*degree, Fraction::of(coefficient));
    }
    let actual = Model(terms);
    assert!(
        actual.same(model),
        "{name}: expected {}, got {}",
        model.text(ring.variable()),
        actual.text(ring.variable())
    );
}

/// The first broken rule of the canonical form of `polynomial`, if any: as
/// many coefficients as degrees, the degrees strictly increasing, no
/// coefficient that the zero test finds zero, `degree` the last degree and
/// `is_zero` exactly for no term.
fn canonical_form<K>(
    ring: &PolynomialRing<K>,
    polynomial: &Polynomial<K>,
    context: &mut Context,
) -> kalyx::Result<Option<String>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let degrees = polynomial.degrees();
    let coefficients = polynomial.coefficients();
    if degrees.len() != coefficients.len() {
        return Ok(Some(format!(
            "{} degrees and {} coefficients",
            degrees.len(),
            coefficients.len()
        )));
    }
    if polynomial.is_zero() != degrees.is_empty() {
        return Ok(Some(format!(
            "is_zero is {} for {} terms",
            polynomial.is_zero(),
            degrees.len()
        )));
    }
    if polynomial.degree() != degrees.last().copied() {
        return Ok(Some(format!(
            "the degree {:?} is not the last degree of {degrees:?}",
            polynomial.degree()
        )));
    }
    for pair in degrees.windows(2) {
        if pair[0] >= pair[1] {
            return Ok(Some(format!("the degrees {degrees:?} do not increase")));
        }
    }
    for (degree, coefficient) in degrees.iter().zip(coefficients) {
        match ring.coefficient_ring().zero_test(coefficient, context)? {
            ZeroTest::Zero => {
                return Ok(Some(format!(
                    "the term of degree {degree} has the coefficient 0"
                )));
            }
            ZeroTest::Nonzero => {}
            ZeroTest::Undecided(reason) => match reason {},
        }
    }
    Ok(None)
}

/// Whether every polynomial of `sides` equals the first: the same degrees,
/// and coefficients whose difference the zero test of the coefficient ring
/// finds zero.
fn agree<K>(
    ring: &PolynomialRing<K>,
    sides: &[(&'static str, Polynomial<K>)],
    context: &mut Context,
) -> kalyx::Result<bool>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let Some((_, first)) = sides.first() else {
        return Ok(true);
    };
    let coefficients = ring.coefficient_ring();
    for (_, side) in sides {
        if side.degrees() != first.degrees()
            || side.coefficients().len() != first.coefficients().len()
        {
            return Ok(false);
        }
        for (a, b) in side.coefficients().iter().zip(first.coefficients()) {
            let difference = coefficients.subtract(a, b, context)?;
            match coefficients.zero_test(&difference, context)? {
                ZeroTest::Zero => {}
                ZeroTest::Nonzero => return Ok(false),
                ZeroTest::Undecided(reason) => match reason {},
            }
        }
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// The properties, generic over the coefficient ring

/// The results of one case of a property, each with its name: the sides of
/// its identity, which must be equal, and its intermediate results.
struct Results<K: CoefficientRing> {
    sides: Vec<(&'static str, Polynomial<K>)>,
    steps: Vec<(&'static str, Polynomial<K>)>,
}

/// $p q$ and $q p$.
fn commutativity<K>(
    ring: &PolynomialRing<K>,
    p: &Polynomial<K>,
    q: &Polynomial<K>,
    context: &mut Context,
) -> kalyx::Result<Results<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let pq = ring.multiply(p, q, context)?;
    let qp = ring.multiply(q, p, context)?;
    Ok(Results {
        sides: vec![("p*q", pq), ("q*p", qp)],
        steps: Vec::new(),
    })
}

/// $(p q) r$ and $p (q r)$.
fn associativity<K>(
    ring: &PolynomialRing<K>,
    p: &Polynomial<K>,
    q: &Polynomial<K>,
    r: &Polynomial<K>,
    context: &mut Context,
) -> kalyx::Result<Results<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let pq = ring.multiply(p, q, context)?;
    let qr = ring.multiply(q, r, context)?;
    let left = ring.multiply(&pq, r, context)?;
    let right = ring.multiply(p, &qr, context)?;
    Ok(Results {
        sides: vec![("(p*q)*r", left), ("p*(q*r)", right)],
        steps: vec![("p*q", pq), ("q*r", qr)],
    })
}

/// $p (q + r)$, $p q + p r$ and $(q + r) p$.
fn distributivity<K>(
    ring: &PolynomialRing<K>,
    p: &Polynomial<K>,
    q: &Polynomial<K>,
    r: &Polynomial<K>,
    context: &mut Context,
) -> kalyx::Result<Results<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let sum = ring.add(q, r, context)?;
    let pq = ring.multiply(p, q, context)?;
    let pr = ring.multiply(p, r, context)?;
    let left = ring.multiply(p, &sum, context)?;
    let right = ring.add(&pq, &pr, context)?;
    let flipped = ring.multiply(&sum, p, context)?;
    Ok(Results {
        sides: vec![("p*(q+r)", left), ("p*q+p*r", right), ("(q+r)*p", flipped)],
        steps: vec![("q+r", sum), ("p*q", pq), ("p*r", pr)],
    })
}

/// $(a p + b q)'$ and $a p' + b q'$, with the scalars as constants.
fn linearity<K>(
    ring: &PolynomialRing<K>,
    a: &K::Element,
    p: &Polynomial<K>,
    b: &K::Element,
    q: &Polynomial<K>,
    context: &mut Context,
) -> kalyx::Result<Results<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let a_constant = ring.constant(a, context)?;
    let b_constant = ring.constant(b, context)?;
    let ap = ring.multiply(&a_constant, p, context)?;
    let bq = ring.multiply(&b_constant, q, context)?;
    let combination = ring.add(&ap, &bq, context)?;
    let left = ring.derivative(&combination, context)?;
    let dp = ring.derivative(p, context)?;
    let dq = ring.derivative(q, context)?;
    let adp = ring.multiply(&a_constant, &dp, context)?;
    let bdq = ring.multiply(&b_constant, &dq, context)?;
    let right = ring.add(&adp, &bdq, context)?;
    Ok(Results {
        sides: vec![("(a*p+b*q)'", left), ("a*p'+b*q'", right)],
        steps: vec![
            ("a*p", ap),
            ("b*q", bq),
            ("a*p+b*q", combination),
            ("p'", dp),
            ("q'", dq),
            ("a*p'", adp),
            ("b*q'", bdq),
        ],
    })
}

/// $(p q)'$ and $p' q + p q'$.
fn product_rule<K>(
    ring: &PolynomialRing<K>,
    p: &Polynomial<K>,
    q: &Polynomial<K>,
    context: &mut Context,
) -> kalyx::Result<Results<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let pq = ring.multiply(p, q, context)?;
    let left = ring.derivative(&pq, context)?;
    let dp = ring.derivative(p, context)?;
    let dq = ring.derivative(q, context)?;
    let dpq = ring.multiply(&dp, q, context)?;
    let pdq = ring.multiply(p, &dq, context)?;
    let right = ring.add(&dpq, &pdq, context)?;
    Ok(Results {
        sides: vec![("(p*q)'", left), ("p'*q+p*q'", right)],
        steps: vec![
            ("p*q", pq),
            ("p'", dp),
            ("q'", dq),
            ("p'*q", dpq),
            ("p*q'", pdq),
        ],
    })
}

/// $(x + 1)^n$ by `power`, with $x + 1$ the sum of `generator` and `one`.
fn binomial_power<K>(
    ring: &PolynomialRing<K>,
    exponent: u64,
    context: &mut Context,
) -> kalyx::Result<Polynomial<K>>
where
    K: CoefficientRing<Undecided = Infallible>,
{
    let x = ring.generator(context)?;
    let one = ring.one(context)?;
    let base = ring.add(&x, &one, context)?;
    ring.power(&base, exponent, context)
}

// ---------------------------------------------------------------------------
// The cases of the properties

/// $p q = q p$; in one case of eight $q = p$, in one of eight $p$ and $q$
/// are conjugates.
fn commutativity_case(case: &mut Case, tally: &mut Tally) {
    let ring = case.ring();
    let step = case.step();
    let (p_input, q_input) = match case.random.below(8) {
        0 => {
            tally.add("squares", 1);
            let p_input = case.input(step);
            let q_input = case.input_of(p_input.terms.clone());
            (p_input, q_input)
        }
        1 => case.conjugates(step, tally),
        _ => (case.input(step), case.input(step)),
    };
    let (p, p_model) = case.build("p", &ring, &p_input, tally);
    let (q, q_model) = case.build("q", &ring, &q_input, tally);
    let results = commutativity(&ring, &p, &q, &mut case.context).expect("the products");
    let expected = p_model.times(&q_model, tally);
    case.verify(&ring, &results, &expected, &[], tally);
}

/// $(p q) r = p (q r)$; in one case of six $p$ and $r$ are conjugates.
fn associativity_case(case: &mut Case, tally: &mut Tally) {
    let ring = case.ring();
    let step = case.step();
    let (p_input, q_input, r_input) = if case.random.chance(1, 6) {
        let (p_input, r_input) = case.conjugates(step, tally);
        (p_input, case.input(step), r_input)
    } else {
        (case.input(step), case.input(step), case.input(step))
    };
    let (p, p_model) = case.build("p", &ring, &p_input, tally);
    let (q, q_model) = case.build("q", &ring, &q_input, tally);
    let (r, r_model) = case.build("r", &ring, &r_input, tally);
    let results = associativity(&ring, &p, &q, &r, &mut case.context).expect("the products");
    let pq = p_model.times(&q_model, tally);
    let qr = q_model.times(&r_model, tally);
    let expected = pq.times(&r_model, tally);
    case.verify(
        &ring,
        &results,
        &expected,
        &[("p*q", pq), ("q*r", qr)],
        tally,
    );
}

/// $p (q + r) = p q + p r = (q + r) p$; $r$ is drawn at random, or is $-q$,
/// $s - q$ for an input $s$ drawn at random, or $q$.
fn distributivity_case(case: &mut Case, tally: &mut Tally) {
    let ring = case.ring();
    let step = case.step();
    let p_input = case.input(step);
    let q_input = case.input(step);
    let r_input = match case.random.below(10) {
        0 | 1 => {
            tally.add("r = -q", 1);
            case.input_of(negated_terms(&q_input.terms))
        }
        2 | 3 => {
            tally.add("r = s - q", 1);
            let mut r_terms = negated_terms(&q_input.terms);
            r_terms.extend(terms(&mut case.random, step));
            case.input_of(r_terms)
        }
        4 => case.input_of(q_input.terms.clone()),
        _ => case.input(step),
    };
    let (p, p_model) = case.build("p", &ring, &p_input, tally);
    let (q, q_model) = case.build("q", &ring, &q_input, tally);
    let (r, r_model) = case.build("r", &ring, &r_input, tally);
    let results = distributivity(&ring, &p, &q, &r, &mut case.context).expect("the operations");
    let sum = q_model.plus(&r_model, tally);
    if sum.is_zero() {
        tally.add("q + r = 0", 1);
    }
    let pq = p_model.times(&q_model, tally);
    let pr = p_model.times(&r_model, tally);
    let expected = p_model.times(&sum, tally);
    case.verify(
        &ring,
        &results,
        &expected,
        &[("q+r", sum), ("p*q", pq), ("p*r", pr)],
        tally,
    );
}

/// $(a p + b q)' = a p' + b q'$; in one case of six $q = p$ and $b = -a$,
/// and $a$ and $b$ are each 0 in one case of ten.
fn linearity_case(case: &mut Case, tally: &mut Tally) {
    let ring = case.ring();
    let step = case.step();
    let p_input = case.input(step);
    let (q_input, a, b) = if case.random.chance(1, 6) {
        let q_input = case.input_of(p_input.terms.clone());
        let a = case.scalar("a", 1, 10);
        let b = a.negated();
        case.inputs.push(format!("b = -a = {}", b.text()));
        (q_input, a, b)
    } else {
        let q_input = case.input(step);
        let a = case.scalar("a", 1, 10);
        let b = case.scalar("b", 1, 10);
        (q_input, a, b)
    };
    if a.is_zero() || b.is_zero() {
        tally.add("a = 0 or b = 0", 1);
    }
    let (p, p_model) = case.build("p", &ring, &p_input, tally);
    let (q, q_model) = case.build("q", &ring, &q_input, tally);
    let a_element = rational(&a, &mut case.context);
    let b_element = rational(&b, &mut case.context);
    let results = linearity(&ring, &a_element, &p, &b_element, &q, &mut case.context)
        .expect("the operations");
    let a_model = Model::constant(&a);
    let b_model = Model::constant(&b);
    let ap = a_model.times(&p_model, tally);
    let bq = b_model.times(&q_model, tally);
    let combination = ap.plus(&bq, tally);
    if combination.is_zero() && !p_model.is_zero() {
        tally.add("a*p + b*q = 0 for p other than 0", 1);
    }
    let dp = p_model.derivative();
    let dq = q_model.derivative();
    let adp = a_model.times(&dp, tally);
    let bdq = b_model.times(&dq, tally);
    let expected = combination.derivative();
    case.verify(
        &ring,
        &results,
        &expected,
        &[
            ("a*p", ap),
            ("b*q", bq),
            ("a*p+b*q", combination),
            ("p'", dp),
            ("q'", dq),
            ("a*p'", adp),
            ("b*q'", bdq),
        ],
        tally,
    );
}

/// $(p q)' = p' q + p q'$; in one case of four $p$ and $q$ are conjugates,
/// in one of eight $q = p$.
fn product_rule_case(case: &mut Case, tally: &mut Tally) {
    let ring = case.ring();
    let step = case.step();
    let (p_input, q_input) = match case.random.below(8) {
        0 | 1 => case.conjugates(step, tally),
        2 => {
            tally.add("squares", 1);
            let p_input = case.input(step);
            let q_input = case.input_of(p_input.terms.clone());
            (p_input, q_input)
        }
        _ => (case.input(step), case.input(step)),
    };
    let (p, p_model) = case.build("p", &ring, &p_input, tally);
    let (q, q_model) = case.build("q", &ring, &q_input, tally);
    let results = product_rule(&ring, &p, &q, &mut case.context).expect("the operations");
    let pq = p_model.times(&q_model, tally);
    let dp = p_model.derivative();
    let dq = q_model.derivative();
    let dpq = dp.times(&q_model, tally);
    let pdq = p_model.times(&dq, tally);
    let expected = pq.derivative();
    case.verify(
        &ring,
        &results,
        &expected,
        &[
            ("p*q", pq),
            ("p'", dp),
            ("q'", dq),
            ("p'*q", dpq),
            ("p*q'", pdq),
        ],
        tally,
    );
}

// ---------------------------------------------------------------------------
// The tests

#[test]
fn products_commute() {
    let tally = run("products_commute", COMMUTATIVITY_SEED, commutativity_case);
    tally.require("products_commute", &REQUIRED);
    tally.require("products_commute", &["squares", "conjugate inputs"]);
}

#[test]
fn products_associate() {
    let tally = run("products_associate", ASSOCIATIVITY_SEED, associativity_case);
    tally.require("products_associate", &REQUIRED);
    tally.require("products_associate", &["conjugate inputs"]);
}

#[test]
fn products_distribute_over_sums() {
    let tally = run(
        "products_distribute_over_sums",
        DISTRIBUTIVITY_SEED,
        distributivity_case,
    );
    tally.require("products_distribute_over_sums", &REQUIRED);
    tally.require(
        "products_distribute_over_sums",
        &["r = -q", "r = s - q", "q + r = 0"],
    );
}

#[test]
fn the_derivative_is_linear() {
    let tally = run("the_derivative_is_linear", LINEARITY_SEED, linearity_case);
    tally.require("the_derivative_is_linear", &REQUIRED);
    tally.require(
        "the_derivative_is_linear",
        &["a = 0 or b = 0", "a*p + b*q = 0 for p other than 0"],
    );
}

#[test]
fn the_derivative_follows_the_product_rule() {
    let tally = run(
        "the_derivative_follows_the_product_rule",
        PRODUCT_RULE_SEED,
        product_rule_case,
    );
    tally.require("the_derivative_follows_the_product_rule", &REQUIRED);
    tally.require(
        "the_derivative_follows_the_product_rule",
        &["squares", "conjugate inputs"],
    );
}

/// Prints the binomial power that failed.
struct BinomialGuard(String);

impl Drop for BinomialGuard {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("the binomial power {} failed", self.0);
        }
    }
}

#[test]
fn powers_of_x_plus_1_have_the_binomial_coefficients() {
    // Row $n$ of Pascal's triangle: $\binom{n}{k}$ for $k = 0, \dots, n$.
    let mut row = vec![Big::from_u64(1)];
    // $2^n$, the sum of row $n$.
    let mut power_of_two = Big::from_u64(1);
    let mut tally = Tally::default();
    for n in 0..BINOMIAL_POWERS {
        let input = format!("(x + 1)^{n}");
        let _guard = BinomialGuard(input.clone());
        assert_eq!(row.len() as u64, n + 1, "the length of the row");
        let mut sum = Big::from_u64(0);
        for coefficient in &row {
            sum = sum.plus(coefficient);
        }
        assert_eq!(sum, power_of_two, "the binomial coefficients add up to 2^n");

        let expected = Model(
            row.iter()
                .enumerate()
                .map(|(k, coefficient)| (k as u64, Fraction::integer(coefficient.clone())))
                .collect(),
        );
        let mut context = context();
        let ring = PolynomialRing::new(Rationals, "x", &mut context).expect("the ring in x");
        let powered = binomial_power(&ring, n, &mut context).expect("the power of x + 1");
        assert_polynomial(
            &format!("{input} by power"),
            &ring,
            &powered,
            &expected,
            &mut context,
        );
        let term = parse(&input, &mut context).expect("the parsed power");
        let expanded = ring
            .expand(&term, &mut context)
            .expect("the expansion of the parsed power");
        assert_polynomial(
            &format!("{input} by expansion"),
            &ring,
            &expanded,
            &expected,
            &mut context,
        );
        tally.add("cases", 1);

        let mut next = vec![Big::from_u64(1)];
        for pair in row.windows(2) {
            next.push(pair[0].plus(&pair[1]));
        }
        next.push(Big::from_u64(1));
        row = next;
        power_of_two = power_of_two.plus(&power_of_two);
    }
    assert_eq!(tally.get("cases"), BINOMIAL_POWERS);
}

#[test]
fn the_reference_agrees_with_values_computed_by_hand() {
    // Integers beyond 64 bits, their products and their decimal text.
    let mut two_to_the_100 = Big::from_u64(1);
    for _ in 0..100 {
        two_to_the_100 = two_to_the_100.plus(&two_to_the_100);
    }
    assert_eq!(two_to_the_100.decimal(), "1267650600228229401496703205376");
    assert_eq!(two_to_the_100.bits(), 101);
    assert_eq!(
        Big::parse("-1267650600228229401496703205376").negated(),
        two_to_the_100
    );
    let product = Big::parse("123456789012345678901234567890")
        .times(&Big::parse("-987654321098765432109876543210"));
    assert_eq!(
        product.decimal(),
        "-121932631137021795226185032733622923332237463801111263526900"
    );
    assert_eq!(
        Big::from_u64(u64::MAX).plus(&Big::from_u64(1)).decimal(),
        "18446744073709551616"
    );
    assert_eq!(Big::from_i64(-5).plus(&Big::from_i64(3)), Big::from_i64(-2));
    assert!(Big::from_i64(7).plus(&Big::from_i64(-7)).is_zero());
    assert_eq!(Big::from_u64(1_000_000_000_000).decimal(), "1000000000000");

    // Fractions divide out the small primes and compare by value.
    assert_eq!(
        Fraction::small(1, 6).plus(&Fraction::small(1, 3)).text(),
        "1/2"
    );
    assert_eq!(Fraction::small(-6, 4).text(), "-3/2");
    assert!(Fraction::small(-6, 4).equals(&Fraction::small(-3, 2)));
    assert!(!Fraction::small(1, 2).equals(&Fraction::small(1, 3)));
    assert!(
        Fraction::small(2, 3)
            .times(&Fraction::small(3, 2))
            .is_integer()
    );

    // $(x + 1)(x - 1) = x^2 - 1$, in which the terms of $x$ cancel.
    let mut tally = Tally::default();
    let one = Fraction::small(1, 1);
    let minus_one = Fraction::small(-1, 1);
    let sum = Model::of_terms(&[(1, one.clone()), (0, one.clone())], &mut tally);
    let difference = Model::of_terms(&[(0, minus_one.clone()), (1, one.clone())], &mut tally);
    let product = sum.times(&difference, &mut tally);
    assert_eq!(product.text("x"), "-1*x^0 + 1*x^2");
    assert_eq!(tally.get(CANCELLED), 1);
    // The terms of an input that cancel are counted apart.
    let zero = Model::of_terms(&[(5, minus_one), (5, one)], &mut tally);
    assert!(zero.is_zero());
    assert_eq!(tally.get("coefficients that cancelled in the inputs"), 1);
    // $((x + 1)^2)' = 2 x + 2$, and $(3/2)' = 0$.
    let square = sum.times(&sum, &mut tally);
    assert_eq!(square.text("x"), "1*x^0 + 2*x^1 + 1*x^2");
    assert_eq!(square.derivative().text("x"), "2*x^0 + 2*x^1");
    assert!(
        Model::constant(&Fraction::small(3, 2))
            .derivative()
            .is_zero()
    );
    // A sparse product whose degrees meet: $(x^{2^{40}} + 1)(x^{2^{40}} - 1)$.
    let high = 1_u64 << 40;
    let mut tally = Tally::default();
    let p = Model::of_terms(
        &[(high, Fraction::small(1, 1)), (0, Fraction::small(1, 1))],
        &mut tally,
    );
    let q = Model::of_terms(
        &[(high, Fraction::small(1, 1)), (0, Fraction::small(-1, 1))],
        &mut tally,
    );
    assert_eq!(
        p.times(&q, &mut tally).text("x"),
        "-1*x^0 + 1*x^2199023255552"
    );
    assert_eq!(tally.get(CANCELLED), 1);
}
