//! Exact integers and rationals: canonical forms, decimal literals, the bit
//! bounds checked before any charge, division by zero, powers and the
//! request context. The rules are those of
//! `docs/components/numbers/contract.md`.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "the helpers of the tests unwrap their results, as the tests do"
)]

use kalyx::context::{CancelFlag, Clock, Storage, StorageCost};
use kalyx::number::{Integer, Rational};
use kalyx::{Context, Error, ErrorKind, FaultKind, LimitAmount, LimitField, LimitId, Limits, Span};

// ---------------------------------------------------------------------------
// Helpers

fn context(limits: Limits) -> Context {
    Context::new(limits, CancelFlag::new())
}

fn default_context() -> Context {
    context(Limits::new())
}

fn bits(max_integer_bits: u64) -> Limits {
    Limits::new().with_max_integer_bits(max_integer_bits)
}

/// The canonical rational $n / d$, built under default limits.
fn q(numerator: i64, denominator: i64) -> Rational {
    Rational::new(
        Integer::from(numerator),
        Integer::from(denominator),
        &mut default_context(),
    )
    .unwrap()
}

fn decimal(text: &str) -> Rational {
    Rational::parse_decimal(text, &mut default_context()).unwrap()
}

/// $2^k$, built under default limits.
fn two_to(k: i64) -> Rational {
    Rational::from(2_i64)
        .power(
            k,
            &mut Context::new(
                Limits::new()
                    .with_max_integer_bits(1 << 20)
                    .with_max_exponent(1 << 20),
                CancelFlag::new(),
            ),
        )
        .unwrap()
}

fn assert_limit(error: &Error, field: LimitField) {
    assert_eq!(error.kind(), ErrorKind::ResourceLimit, "{error}");
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.id(), &LimitId::Field(field), "{error}");
}

fn assert_fault(error: &Error, fault: FaultKind) {
    assert_eq!(error.kind(), ErrorKind::Fault(fault), "{error}");
}

/// A clock that always reads the same time.
struct FixedClock(u64);

impl Clock for FixedClock {
    fn now(&mut self) -> u64 {
        self.0
    }

    fn fork(&self) -> Box<dyn Clock> {
        Box::new(FixedClock(self.0))
    }
}

/// A context whose deadline has passed.
fn expired() -> Context {
    Context::with_observers(
        Limits::new(),
        Box::new(FixedClock(10)),
        Box::new(CancelFlag::new()),
    )
    .with_deadline(5)
}

// ---------------------------------------------------------------------------
// The bit bound is checked before the charge and before any allocation

#[test]
fn an_addition_beyond_max_integer_bits_is_rejected_before_any_charge() {
    let a = two_to(63);
    let mut context = context(bits(64));
    context.charge(5).unwrap();
    // max(64 + 1, 64 + 1) + 1 = 66 bits for 2^63 + 2^63.
    let error = a.add(&a, &mut context).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    let exceeded = error.exceeded().unwrap();
    assert_eq!(exceeded.allowed(), 64);
    assert_eq!(exceeded.amount(), LimitAmount::Required(66));
    assert_eq!(context.work_used(), 5);
    // With the bound admitted, the sum 2^64 is computed and charged.
    let mut wide = context_with_bits(66);
    assert_eq!(a.add(&a, &mut wide).unwrap(), two_to(64));
    assert_eq!(wide.work_used(), 1);
}

#[test]
fn a_multiplication_beyond_max_integer_bits_is_rejected_before_any_charge() {
    let a = two_to(40);
    let mut context = context(bits(64));
    context.charge(5).unwrap();
    // 41 + 41 = 82 bits for 2^40 * 2^40.
    let error = a.multiply(&a, &mut context).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(82)
    );
    assert_eq!(context.work_used(), 5);
    let fits = two_to(20).multiply(&a, &mut context).unwrap();
    assert_eq!(fits, two_to(60));
    assert_eq!(context.work_used(), 6);
}

#[test]
fn a_sum_whose_denominators_dominate_is_rejected_before_any_charge() {
    // 1/7 + 1/9 = 16/63: max(|1| + |9|, |1| + |7|) + 1 = 6, and |7| + |9| = 7.
    let (a, b) = (q(1, 7), q(1, 9));
    let mut narrow = context(bits(6));
    let errors = [
        a.add(&b, &mut narrow).unwrap_err(),
        a.subtract(&b, &mut narrow).unwrap_err(),
        a.compare(&b, &mut narrow).unwrap_err(),
    ];
    for error in errors {
        assert_limit(&error, LimitField::IntegerBits);
        assert_eq!(error.exceeded().unwrap().amount(), LimitAmount::Required(7));
    }
    assert_eq!(narrow.work_used(), 0);
    assert_eq!(a.add(&b, &mut context(bits(7))).unwrap(), q(16, 63));
}

#[test]
fn a_quotient_is_bounded_by_its_crossed_parts() {
    // (2/9) / (8/3) = 1/12: max(|2| + |3|, |9| + |8|) = 8 bits.
    let mut narrow = context(bits(7));
    let error = q(2, 9).divide(&q(8, 3), &mut narrow).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(error.exceeded().unwrap().amount(), LimitAmount::Required(8));
    assert_eq!(narrow.work_used(), 0);
    assert_eq!(
        q(2, 9).divide(&q(8, 3), &mut context(bits(8))).unwrap(),
        q(1, 12)
    );
}

#[test]
fn a_power_beyond_max_integer_bits_is_rejected_before_any_charge() {
    let mut context = default_context();
    context.charge(5).unwrap();
    // 2^4096 has 4097 bits; the default limit is 4096.
    let error = Rational::from(2_i64).power(4096, &mut context).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(4097)
    );
    assert_eq!(context.work_used(), 5);
    // A rational base: (3/2)^-2000 is 2^2000 / 3^2000, whose numerator has 2001 bits
    // and whose denominator has 3170.
    let mut context = context_with_bits(3169);
    let error = q(3, 2).power(-2000, &mut context).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(context.work_used(), 0);
    let mut context = context_with_bits(3171);
    let value = q(3, 2).power(-2000, &mut context).unwrap();
    assert_eq!(value.numerator().bits(), 2001);
    assert_eq!(value.denominator().bits(), 3170);
    // (2/3)^2000: the bound of the denominator, 3^2000 of 3170 bits, decides.
    let mut context = context_with_bits(3169);
    let error = q(2, 3).power(2000, &mut context).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(context.work_used(), 0);
    // 2^(2^40) could not be computed at all, so only a check before the
    // computation can reject it.
    let mut context = Context::new(Limits::new().with_max_exponent(u64::MAX), CancelFlag::new());
    context.charge(5).unwrap();
    let error = Rational::from(2_i64)
        .power(1 << 40, &mut context)
        .unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required((1 << 40) + 1)
    );
    assert_eq!(context.work_used(), 5);
    // A bound beyond u64::MAX exceeds every limit, even u64::MAX.
    let mut unlimited = Context::new(
        Limits::new()
            .with_max_exponent(u64::MAX)
            .with_max_integer_bits(u64::MAX),
        CancelFlag::new(),
    );
    let error = Rational::from(5_i64)
        .power(i64::MAX, &mut unlimited)
        .unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Bound(u64::MAX)
    );
    assert_eq!(unlimited.work_used(), 0);
}

fn context_with_bits(max_integer_bits: u64) -> Context {
    context(bits(max_integer_bits))
}

#[test]
fn the_power_checks_the_exponent_then_the_zero_base_then_the_bits() {
    let mut context = context(Limits::new().with_max_exponent(10).with_max_integer_bits(0));
    let error = Rational::from(0_i64).power(-11, &mut context).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    let error = Rational::from(0_i64).power(-10, &mut context).unwrap_err();
    assert_fault(&error, FaultKind::DivisionByZero);
    let error = Rational::from(0_i64).power(10, &mut context).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(context.work_used(), 0);
    let error = Rational::from(1_i64)
        .power(i64::MIN, &mut default_context())
        .unwrap_err();
    assert_limit(&error, LimitField::Exponent);
    assert_eq!(
        error.exceeded().unwrap().amount(),
        LimitAmount::Required(1 << 63)
    );
}

// ---------------------------------------------------------------------------
// Decimal literals and division by zero

#[test]
fn decimal_literals_add_exactly() {
    let mut context = default_context();
    let tenth = Rational::parse_decimal("0.1", &mut context).unwrap();
    let fifth = Rational::parse_decimal("0.2", &mut context).unwrap();
    assert_eq!(tenth, q(1, 10));
    let sum = tenth.add(&fifth, &mut context).unwrap();
    assert_eq!(sum, q(3, 10));
    assert_eq!(sum.to_string(), "3/10");
    assert_eq!(sum.numerator(), &Integer::from(3_i64));
    assert_eq!(sum.denominator(), &Integer::from(10_i64));
}

#[test]
fn division_by_zero_fails_before_any_charge() {
    let zero = Rational::from(0_i64);
    let one = Rational::from(1_i64);
    // No work is left, so any charge would fail with ResourceLimit instead.
    let mut context = context(Limits::new().with_max_work(0).with_max_integer_bits(0));
    for error in [
        one.divide(&zero, &mut context).unwrap_err(),
        zero.divide(&zero, &mut context).unwrap_err(),
        zero.inverse(&mut context).unwrap_err(),
        Rational::new(Integer::from(1_i64), Integer::from(0_i64), &mut context).unwrap_err(),
        Rational::new(Integer::from(0_i64), Integer::from(0_i64), &mut context).unwrap_err(),
        zero.power(-1, &mut context).unwrap_err(),
        zero.power(-5, &mut context).unwrap_err(),
    ] {
        assert_fault(&error, FaultKind::DivisionByZero);
        assert!(error.exceeded().is_none());
    }
    assert_eq!(context.work_used(), 0);
}

#[test]
fn malformed_decimal_literals_are_syntax_errors_with_spans() {
    for (source, start, end) in [
        ("", 0, 0),
        (".5", 0, 1),
        ("1.", 2, 2),
        ("1e-3", 1, 2),
        ("1.2.3", 3, 4),
        ("-1", 0, 1),
        ("+1", 0, 1),
        (" 1", 0, 1),
        ("1 ", 1, 2),
        ("12x", 2, 3),
        ("\u{0661}", 0, 2),
        ("0x10", 1, 2),
    ] {
        let mut context = context(Limits::new().with_max_work(0));
        let error = Rational::parse_decimal(source, &mut context).unwrap_err();
        assert_fault(&error, FaultKind::Syntax);
        assert_eq!(error.span(), Span::new(start, end), "{source:?}");
        assert_eq!(context.work_used(), 0);
    }
}

#[test]
fn literals_charge_one_unit_per_digit_after_the_bit_check() {
    let mut budget = default_context();
    assert_eq!(
        Rational::parse_decimal("001.2500", &mut budget).unwrap(),
        q(5, 4)
    );
    assert_eq!(budget.work_used(), 7);
    let mut short = context(Limits::new().with_max_work(6));
    let error = Rational::parse_decimal("001.2500", &mut short).unwrap_err();
    assert_limit(&error, LimitField::Work);
    assert_eq!(short.work_used(), 0);
    // Seven digits need 28 bits; the bit check comes before the charge.
    let mut narrow = context(bits(27));
    let error = Rational::parse_decimal("001.2500", &mut narrow).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(narrow.work_used(), 0);
}

// ---------------------------------------------------------------------------
// Canonical forms, display and storage

#[test]
fn rationals_are_canonical_and_displayed_deterministically() {
    for (n, d, numerator, denominator, text) in [
        (2_i64, 4_i64, 1_i64, 2_i64, "1/2"),
        (-6, -12, 1, 2, "1/2"),
        (6, -4, -3, 2, "-3/2"),
        (0, -7, 0, 1, "0"),
        (10, 5, 2, 1, "2"),
        (-9, 3, -3, 1, "-3"),
        (i64::MIN, i64::MIN, 1, 1, "1"),
    ] {
        let value = q(n, d);
        assert_eq!(value.numerator(), &Integer::from(numerator), "{n}/{d}");
        assert_eq!(value.denominator(), &Integer::from(denominator), "{n}/{d}");
        assert_eq!(value.to_string(), text);
        assert_eq!(value, q(numerator, denominator));
    }
    assert!(q(3, 4).is_positive());
    assert!(q(-3, 4).is_negative());
    assert!(q(0, 4).is_zero());
    assert!(q(8, 4).is_integer());
    assert!(!q(3, 4).is_integer());
    assert_eq!(Integer::from(u64::MAX).to_string(), "18446744073709551615");
    assert_eq!(Integer::from(i64::MIN).to_string(), "-9223372036854775808");
    assert_eq!(Integer::from(0_i64).bits(), 0);
    assert_eq!(Integer::from(i64::MIN).bits(), 64);
    assert_eq!(format!("{:?}", q(-3, 6)), format!("{:?}", q(1, -2)));
}

#[test]
fn rationals_are_ordered_by_value() {
    let values = [
        q(-5, 2),
        q(-2, 1),
        q(-1, 3),
        q(0, 1),
        q(1, 3),
        q(1, 2),
        q(2, 1),
    ];
    for (i, left) in values.iter().enumerate() {
        for (j, right) in values.iter().enumerate() {
            let mut context = default_context();
            assert_eq!(
                left.compare(right, &mut context).unwrap(),
                i.cmp(&j),
                "{left} {right}"
            );
            assert_eq!(context.work_used(), 1);
        }
    }
}

#[test]
fn the_storage_cost_follows_the_formula_of_the_context() {
    // (1, |n| + |d| + 3) for n/d.
    assert_eq!(q(0, 1).storage(), Storage::new(1, 4));
    assert_eq!(q(1, 1).storage(), Storage::new(1, 5));
    assert_eq!(q(-3, 4).storage(), Storage::new(1, 8));
    assert_eq!(two_to(-100).storage(), Storage::new(1, 1 + 101 + 3));
}

#[test]
fn operations_charge_one_unit_and_powers_by_their_exponent() {
    let mut context = default_context();
    let (a, b) = (q(1, 3), q(-2, 5));
    a.add(&b, &mut context).unwrap();
    a.subtract(&b, &mut context).unwrap();
    a.multiply(&b, &mut context).unwrap();
    a.divide(&b, &mut context).unwrap();
    a.negate(&mut context).unwrap();
    a.inverse(&mut context).unwrap();
    Rational::new(Integer::from(2_i64), Integer::from(6_i64), &mut context).unwrap();
    assert_eq!(context.work_used(), 7);
    // 1 + |5| + w(5) = 1 + 3 + 2.
    let mut context = default_context();
    assert_eq!(a.power(-5, &mut context).unwrap(), q(243, 1));
    assert_eq!(context.work_used(), 6);
    let mut context = default_context();
    assert_eq!(a.power(0, &mut context).unwrap(), q(1, 1));
    assert_eq!(context.work_used(), 1);
}

// ---------------------------------------------------------------------------
// Carried over from the tests of exact arithmetic of the earlier
// implementation, with the number API in place of parsed expressions.

#[test]
fn ex1_sums_are_reduced_to_lowest_terms() {
    let sum = q(1, 3).add(&q(1, 6), &mut default_context()).unwrap();
    assert_eq!(sum, q(1, 2));
    assert_eq!(
        (sum.numerator(), sum.denominator()),
        (&Integer::from(1_i64), &Integer::from(2_i64))
    );
    assert_eq!(sum.to_string(), "1/2");
}

#[test]
fn ex2_decimal_literals_are_exact_rationals() {
    let mut context = default_context();
    let sum = decimal("0.1").add(&decimal("0.2"), &mut context).unwrap();
    assert_eq!(sum.to_string(), "3/10");
    let divisor = decimal("0.50").negate(&mut context).unwrap();
    assert_eq!(
        decimal("001.2500").divide(&divisor, &mut context).unwrap(),
        q(-5, 2)
    );
}

#[test]
fn ex3_integer_powers_use_the_empty_product() {
    let mut context = default_context();
    assert_eq!(q(2, 3).power(-5, &mut context).unwrap(), q(243, 32));
    assert_eq!(q(0, 1).power(0, &mut context).unwrap(), q(1, 1));
    let power = q(2, 1).power(100, &mut context).unwrap();
    assert_eq!(power.to_string(), (1_u128 << 100).to_string());
    assert_eq!(power.to_string(), "1267650600228229401496703205376");
}

#[test]
fn ex5_growth_is_checked_before_arithmetic() {
    // The bound of 1 + 1 is max(|1| + |1|, |1| + |1|) + 1 = 3 bits.
    let one = Rational::from(1_i64);
    let error = one.add(&one, &mut context(bits(2))).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(error.exceeded().unwrap().amount(), LimitAmount::Required(3));
    assert_eq!(one.add(&one, &mut context(bits(3))).unwrap(), q(2, 1));
    let error = q(2, 1).power(4097, &mut default_context()).unwrap_err();
    assert_limit(&error, LimitField::Exponent);
}

#[test]
fn rational_operations_match_small_integer_oracle() {
    fn normalized(mut numerator: i64, mut denominator: i64) -> String {
        if denominator < 0 {
            numerator = -numerator;
            denominator = -denominator;
        }
        let (mut a, mut b) = (numerator.unsigned_abs(), denominator.unsigned_abs());
        while b != 0 {
            (a, b) = (b, a % b);
        }
        let a = i64::try_from(a).unwrap();
        numerator /= a;
        denominator /= a;
        if denominator == 1 {
            numerator.to_string()
        } else {
            format!("{numerator}/{denominator}")
        }
    }
    let mut context = default_context();
    for a in -4..=4_i64 {
        for b in -4..=4_i64 {
            for c in 1..=4_i64 {
                for d in 1..=4_i64 {
                    let (left, right) = (q(a, c), q(b, d));
                    for (value, numerator, denominator) in [
                        (left.add(&right, &mut context), a * d + b * c, c * d),
                        (left.subtract(&right, &mut context), a * d - b * c, c * d),
                        (left.multiply(&right, &mut context), a * b, c * d),
                    ] {
                        assert_eq!(
                            value.unwrap().to_string(),
                            normalized(numerator, denominator),
                            "({a}/{c}), ({b}/{d})"
                        );
                    }
                    if b != 0 {
                        assert_eq!(
                            left.divide(&right, &mut context).unwrap().to_string(),
                            normalized(a * d, c * b),
                            "({a}/{c}) / ({b}/{d})"
                        );
                    }
                }
            }
        }
    }
}

/// A recursive-descent evaluator of the fixture's expressions through the
/// number API: sums and differences of products and quotients of factors, a
/// factor being a negation, a parenthesized expression or a decimal literal,
/// optionally raised to an integer power.
struct Evaluator<'a> {
    text: &'a [u8],
    at: usize,
}

impl Evaluator<'_> {
    fn peek(&self) -> Option<u8> {
        self.text.get(self.at).copied()
    }

    fn expression(&mut self, context: &mut Context) -> Rational {
        let mut value = self.term(context);
        loop {
            let operation: fn(&Rational, &Rational, &mut Context) -> kalyx::Result<Rational> =
                match self.peek() {
                    Some(b'+') => Rational::add,
                    Some(b'-') => Rational::subtract,
                    _ => return value,
                };
            self.at += 1;
            let right = self.term(context);
            value = operation(&value, &right, context).unwrap();
        }
    }

    fn term(&mut self, context: &mut Context) -> Rational {
        let mut value = self.factor(context);
        loop {
            let operation: fn(&Rational, &Rational, &mut Context) -> kalyx::Result<Rational> =
                match self.peek() {
                    Some(b'*') => Rational::multiply,
                    Some(b'/') => Rational::divide,
                    _ => return value,
                };
            self.at += 1;
            let right = self.factor(context);
            value = operation(&value, &right, context).unwrap();
        }
    }

    fn factor(&mut self, context: &mut Context) -> Rational {
        if self.peek() == Some(b'-') {
            self.at += 1;
            return self.factor(context).negate(context).unwrap();
        }
        let base = self.primary(context);
        if self.peek() != Some(b'^') {
            return base;
        }
        self.at += 1;
        let exponent = self.factor(context);
        assert!(exponent.is_integer());
        let exponent: i64 = exponent.to_string().parse().unwrap();
        base.power(exponent, context).unwrap()
    }

    fn primary(&mut self, context: &mut Context) -> Rational {
        if self.peek() == Some(b'(') {
            self.at += 1;
            let value = self.expression(context);
            assert_eq!(self.peek(), Some(b')'));
            self.at += 1;
            return value;
        }
        let start = self.at;
        while matches!(self.peek(), Some(b'0'..=b'9' | b'.')) {
            self.at += 1;
        }
        let text = std::str::from_utf8(&self.text[start..self.at]).unwrap();
        Rational::parse_decimal(text, context).unwrap()
    }
}

/// The header row of `tests/fixtures/integer_paths.tsv`, its first line.
const INTEGER_PATHS_HEADER: &str = "id\tsource\tnumerator\tdenominator";

/// Reads the rows of an integer-path fixture, rejecting the first line that
/// breaks the format. The file is plain TSV: the header row, then one row of
/// four columns per line, with no comment or empty lines, so that any TSV
/// reader takes the first line as the header.
fn integer_path_rows(text: &str) -> Result<Vec<[&str; 4]>, String> {
    let mut lines = text.lines().enumerate();
    match lines.next() {
        Some((_, line)) if line == INTEGER_PATHS_HEADER => {}
        _ => return Err("line 1: expected the header row".to_owned()),
    }
    let mut names = std::collections::HashSet::new();
    let mut rows = Vec::new();
    for (index, line) in lines {
        let at = format!("line {}", index + 1);
        if line.is_empty() || line.starts_with('#') {
            return Err(format!("{at}: an empty or comment line"));
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let [name, source, numerator, denominator] = fields.as_slice() else {
            return Err(format!("{at}: {} columns instead of 4", fields.len()));
        };
        if !names.insert(*name) {
            return Err(format!("{at}: duplicate row {name}"));
        }
        rows.push([*name, *source, *numerator, *denominator]);
    }
    Ok(rows)
}

#[test]
fn integer_paths_fixture_rejects_a_missing_commented_or_late_header() {
    let row = "a\t1+2\t3\t1\n";
    let missing = integer_path_rows(row).unwrap_err();
    assert!(
        missing.contains("line 1: expected the header row"),
        "{missing}"
    );
    let commented = integer_path_rows(&format!("# {INTEGER_PATHS_HEADER}\n{row}")).unwrap_err();
    assert!(
        commented.contains("line 1: expected the header row"),
        "{commented}"
    );
    let late = integer_path_rows(&format!("# sources\n{INTEGER_PATHS_HEADER}\n")).unwrap_err();
    assert!(late.contains("line 1: expected the header row"), "{late}");
}

#[test]
fn integer_paths_fixture_rejects_comment_and_empty_lines_after_the_header() {
    let row = "a\t1+2\t3\t1\n";
    let comment =
        integer_path_rows(&format!("{INTEGER_PATHS_HEADER}\n# a note\n{row}")).unwrap_err();
    assert!(
        comment.contains("line 2: an empty or comment line"),
        "{comment}"
    );
    let empty = integer_path_rows(&format!("{INTEGER_PATHS_HEADER}\n\n{row}")).unwrap_err();
    assert!(
        empty.contains("line 2: an empty or comment line"),
        "{empty}"
    );
    let trailing = integer_path_rows(&format!("{INTEGER_PATHS_HEADER}\n{row}\n")).unwrap_err();
    assert!(
        trailing.contains("line 3: an empty or comment line"),
        "{trailing}"
    );
}

#[test]
fn integer_paths_fixture_rejects_a_row_of_five_columns_and_a_duplicate_id() {
    let five =
        integer_path_rows(&format!("{INTEGER_PATHS_HEADER}\na\t1+2\t3\t1\t9\n")).unwrap_err();
    assert!(five.contains("line 2: 5 columns instead of 4"), "{five}");
    let duplicate = integer_path_rows(&format!(
        "{INTEGER_PATHS_HEADER}\na\t1+2\t3\t1\na\t2+2\t4\t1\n"
    ))
    .unwrap_err();
    assert!(duplicate.contains("line 3: duplicate row a"), "{duplicate}");
}

#[test]
fn integer_and_mixed_paths_match_independent_exact_answers() {
    let rows = integer_path_rows(include_str!("fixtures/integer_paths.tsv")).unwrap();
    for [name, source, numerator, denominator] in &rows {
        let mut context = default_context();
        let mut evaluator = Evaluator {
            text: source.as_bytes(),
            at: 0,
        };
        let value = evaluator.expression(&mut context);
        assert_eq!(evaluator.at, source.len(), "{name}: trailing text");
        // Compare the parts as well as the value: an unreduced value or a
        // negative denominator must not pass.
        assert_eq!(value.numerator().to_string(), *numerator, "{name}");
        assert_eq!(value.denominator().to_string(), *denominator, "{name}");
    }
    assert_eq!(rows.len(), 518);
}

#[test]
fn power_bound_is_exact_for_powers_of_two_at_the_default_bit_limit() {
    // 2^4095 has 4096 bits and is admitted; 2^4096 has 4097 bits.
    let two = Rational::from(2_i64);
    assert_eq!(
        two.power(4094, &mut default_context()).unwrap(),
        two_to(4094)
    );
    assert_eq!(
        two.power(4095, &mut default_context())
            .unwrap()
            .numerator()
            .bits(),
        4096
    );
    let error = two.power(4096, &mut default_context()).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    // 10^1200 has 3987 bits, within one bit of its bound.
    let power = Rational::from(10_i64)
        .power(1200, &mut default_context())
        .unwrap();
    assert_eq!(power.numerator().bits(), 3987);
}

#[test]
fn literals_reserve_four_bits_per_decimal_digit() {
    let parsed =
        |max_integer_bits| Rational::parse_decimal("0.25", &mut context(bits(max_integer_bits)));
    assert_eq!(parsed(12).unwrap(), q(1, 4));
    let error = parsed(11).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    assert_eq!(error.span(), Span::new(0, 4));
}

#[test]
fn literal_word_boundaries_preserve_values_and_input_growth_limits() {
    for (source, expected) in [
        ("0", "0"),
        ("00000000000000000000", "0"),
        ("000000000000000000001", "1"),
        ("4294967295", "4294967295"),
        ("4294967296", "4294967296"),
        ("18446744073709551615", "18446744073709551615"),
        ("18446744073709551616", "18446744073709551616"),
        ("99999999999999999999", "99999999999999999999"),
        ("100000000000000000000", "100000000000000000000"),
        (
            "340282366920938463463374607431768211455",
            "340282366920938463463374607431768211455",
        ),
        (
            "340282366920938463463374607431768211456",
            "340282366920938463463374607431768211456",
        ),
        ("0000000000000000000000000000000000000001", "1"),
    ] {
        let required_bits = 4 * source.len() as u64;
        let mut sufficient = context(bits(required_bits));
        let result = Rational::parse_decimal(source, &mut sufficient).unwrap();
        assert_eq!(result.numerator().to_string(), expected, "{source}");
        assert_eq!(result.denominator().to_string(), "1", "{source}");
        let error =
            Rational::parse_decimal(source, &mut context(bits(required_bits - 1))).unwrap_err();
        assert_limit(&error, LimitField::IntegerBits);
    }
}

#[test]
fn integer_shortcuts_keep_conservative_growth_checks() {
    // In each case the result would fit in fewer bits than the bound.
    type Operation = fn(&Rational, &Rational, &mut Context) -> kalyx::Result<Rational>;
    let cases: [(i64, Operation, i64, u64, &str); 5] = [
        (1, Rational::add, 1, 3, "2"),
        (0, Rational::multiply, 0, 2, "0"),
        (255, Rational::subtract, 255, 10, "0"),
        (8, Rational::divide, 1, 5, "8"),
        (8, Rational::divide, -1, 5, "-8"),
    ];
    for (left, operation, right, required_bits, expected) in cases {
        let (left, right) = (Rational::from(left), Rational::from(right));
        let error = operation(&left, &right, &mut context(bits(required_bits - 1))).unwrap_err();
        assert_limit(&error, LimitField::IntegerBits);
        let value = operation(&left, &right, &mut context(bits(required_bits))).unwrap();
        assert_eq!(value.to_string(), expected);
    }
    let error = Rational::parse_decimal("0001", &mut context(bits(15))).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
}

#[test]
fn operands_are_checked_against_the_receiving_limits() {
    // 12345 needs 14 bits; the receiving context allows 13.
    let value = Rational::parse_decimal("12345", &mut default_context()).unwrap();
    let mut receiving = context(bits(13));
    let error = value
        .add(&Rational::from(1_i64), &mut receiving)
        .unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    let error = value.negate(&mut receiving).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    let error = value.inverse(&mut receiving).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    // The exponent 0 ignores the value of the base, but not its bits.
    let error = value.power(0, &mut receiving).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    let error = Rational::new(
        Integer::from(12345_i64),
        Integer::from(1_i64),
        &mut receiving,
    )
    .unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    // 1/12345: the 14 bits are in the denominator.
    let reciprocal = q(1, 12345);
    for error in [
        reciprocal.negate(&mut receiving).unwrap_err(),
        reciprocal.inverse(&mut receiving).unwrap_err(),
        Rational::new(
            Integer::from(1_i64),
            Integer::from(12345_i64),
            &mut receiving,
        )
        .unwrap_err(),
    ] {
        assert_limit(&error, LimitField::IntegerBits);
    }
    assert_eq!(receiving.work_used(), 0);
}

#[test]
fn computational_growth_is_bounded() {
    let error = q(2, 1).power(100, &mut context(bits(32))).unwrap_err();
    assert_limit(&error, LimitField::IntegerBits);
    let error = q(1, 1)
        .power(1000, &mut context(Limits::new().with_max_exponent(10)))
        .unwrap_err();
    assert_limit(&error, LimitField::Exponent);
}

#[test]
fn deadline_and_exhausted_budget_prevent_results() {
    let (one, two) = (q(1, 1), q(2, 1));
    let error = one.add(&two, &mut expired()).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::DeadlineExceeded);
    let mut small = context(Limits::new().with_max_work(0));
    let error = one.add(&two, &mut small).unwrap_err();
    assert_limit(&error, LimitField::Work);
    let consumed = small.work_used();
    assert!(one.add(&two, &mut small).is_err());
    assert!(small.work_used() >= consumed);
}

#[test]
fn integer_paths_still_observe_work_cancellation_and_errors() {
    let (one, two) = (q(1, 1), q(2, 1));
    let error = one
        .add(&two, &mut context(Limits::new().with_max_work(0)))
        .unwrap_err();
    assert_limit(&error, LimitField::Work);
    let flag = CancelFlag::new();
    flag.cancel();
    let mut cancelled = Context::new(Limits::new(), flag);
    assert_eq!(
        one.add(&two, &mut cancelled).unwrap_err().kind(),
        ErrorKind::Cancelled
    );
    assert_eq!(cancelled.work_used(), 0);
    assert_eq!(
        one.add(&two, &mut expired()).unwrap_err().kind(),
        ErrorKind::DeadlineExceeded
    );
    let mut context = default_context();
    let zero = q(0, 1);
    let one_minus_one = one.subtract(&one, &mut context).unwrap();
    let errors = [
        q(8, 1).divide(&zero, &mut context).unwrap_err(),
        zero.divide(&one_minus_one, &mut context).unwrap_err(),
        one.divide(&zero, &mut context).unwrap_err(),
        zero.power(-1, &mut context).unwrap_err(),
    ];
    for error in errors {
        assert_fault(&error, FaultKind::DivisionByZero);
    }
}
