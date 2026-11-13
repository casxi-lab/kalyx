//! Tests of the function registry. The expected names, order and arities,
//! the slots and the identity list are written out from the tables of the
//! contract of the registry, `docs/components/registry/contract.md`, and the
//! reserved words from the words by position of the architecture, not taken
//! from the tables under test.

use super::*;
use crate::{ErrorKind, FaultKind, Result, Span};

/// The records of the contract in their order, with their names and
/// arities.
const KEYS: [(FunctionId, &str, usize); 11] = [
    (FunctionId::Sin, "sin", 1),
    (FunctionId::Cos, "cos", 1),
    (FunctionId::Tan, "tan", 1),
    (FunctionId::Asin, "asin", 1),
    (FunctionId::Acos, "acos", 1),
    (FunctionId::Atan, "atan", 1),
    (FunctionId::Exp, "exp", 1),
    (FunctionId::Log, "log", 1),
    (FunctionId::Sqrt, "sqrt", 1),
    (FunctionId::Rootn, "rootn", 2),
    (FunctionId::Abs, "abs", 1),
];

/// The special forms, whose heads are calls of the class `Formal` without a
/// record.
const SPECIAL_FORMS: [&str; 3] = ["piecewise", "derivative", "substitute"];

/// The words of the table of words by position in the architecture other
/// than the names of the registered functions and the special forms: the
/// constants and `undefined`, the literal heads, the truth values and the
/// condition heads, the heads of other start symbols, the generator `a` and
/// the names that are never constants. The predicates `is_<name>` are
/// checked by their prefix.
const RESERVED: [&str; 30] = [
    "pi",
    "i",
    "undefined",
    "root",
    "croot",
    "true",
    "false",
    "and",
    "or",
    "not",
    "defined",
    "field",
    "field_element",
    "Icc",
    "Ico",
    "Ioc",
    "Ioo",
    "Ici",
    "Iic",
    "Ioi",
    "Iio",
    "union",
    "reals",
    "a",
    "e",
    "E",
    "I",
    "Pi",
    "inf",
    "empty",
];

/// Names of no record: near misses of registered names, other function names
/// and inputs that are not identifiers.
const NON_NAMES: [&str; 52] = [
    "",
    "s",
    "si",
    "sinh",
    "cosh",
    "tanh",
    "asinh",
    "acosh",
    "atanh",
    "arcsin",
    "arccos",
    "arctan",
    "atan2",
    "Sin",
    "SIN",
    "sIn",
    "Exp",
    "LOG",
    "Abs",
    "ln",
    "log10",
    "log2",
    "lg",
    "exp2",
    "expm1",
    "sq",
    "sqr",
    "sqrtn",
    "cbrt",
    "root",
    "roots",
    "rootn2",
    "nroot",
    "abs_",
    "_abs",
    "fabs",
    "sec",
    "csc",
    "cot",
    "sinc",
    "x",
    "y",
    "f",
    "foo",
    "is_real",
    "is_positive",
    "sin ",
    " sin",
    "sin\0",
    "rootn\0\0\0",
    "sin(x)",
    "cosine",
];

/// The name of the key of a record.
fn name(record: FunctionRecord) -> &'static str {
    KEYS.iter()
        .find(|key| key.0 == record.id)
        .expect("every record has a key")
        .1
}

/// The name bytes of a record, up to its length.
fn bytes(record: &FunctionRecord) -> &[u8] {
    &record.name[..record.length]
}

#[test]
fn records_follow_the_keys_of_the_contract() {
    assert_eq!(RECORDS.len(), KEYS.len());
    for (index, (id, key, arity)) in KEYS.into_iter().enumerate() {
        let entry = RECORDS[index];
        assert_eq!(entry.id, id, "record {index}");
        assert_eq!(bytes(&entry), key.as_bytes(), "record {index}");
        assert_eq!(entry.arity, arity, "{key}");
        assert_eq!(id as usize, index, "the identifier of {key}");
        let copy = record(id);
        assert_eq!(copy.id, id, "{key}");
        assert_eq!(bytes(&copy), key.as_bytes(), "{key}");
        assert_eq!(name(copy), key);
    }
}

#[test]
fn names_are_unique_padded_identifiers() {
    for (index, entry) in RECORDS.iter().enumerate() {
        let key = name(*entry);
        assert!((1..=entry.name.len()).contains(&entry.length), "{key}");
        assert!(
            entry.name[entry.length..].iter().all(|&b| b == 0),
            "{key} is padded with zero bytes"
        );
        // The lexer reads an ASCII letter followed by letters, digits and `_`
        // as one name; a registered name starts with a letter.
        assert!(entry.name[0].is_ascii_alphabetic(), "{key}");
        assert!(
            bytes(entry)
                .iter()
                .all(|&b| b.is_ascii_alphanumeric() || b == b'_'),
            "{key}"
        );
        for other in &RECORDS[index + 1..] {
            assert_ne!(bytes(entry), bytes(other), "{key} is registered twice");
        }
    }
}

#[test]
fn lookup_finds_exactly_the_registered_names() {
    for (id, key, _) in KEYS {
        assert_eq!(lookup(key.as_bytes()), Some(id), "{key}");
        // The entry finds the same record.
        let found = resolve(key.as_bytes(), Span::new(0, key.len()));
        assert_eq!(found.ok(), Some(id), "{key}");
    }
    for s in NON_NAMES {
        assert_eq!(lookup(s.as_bytes()), None, "{s:?}");
    }
}

#[test]
fn only_rootn_takes_a_degree() {
    for (id, key, _) in KEYS {
        let entry = record(id);
        if key == "rootn" {
            assert_eq!(entry.arity, 2);
            assert_eq!(entry.roles, [FunctionRole::Operand, FunctionRole::Degree]);
        } else {
            assert_eq!(entry.arity, 1, "{key}");
            // The second position is unused and holds `Operand`.
            assert_eq!(
                entry.roles,
                [FunctionRole::Operand, FunctionRole::Operand],
                "{key}"
            );
        }
    }
}

#[test]
fn registered_names_are_not_reserved() {
    for s in SPECIAL_FORMS.into_iter().chain(RESERVED) {
        assert_eq!(lookup(s.as_bytes()), None, "{s}");
    }
    // Predicates are written `is_<name>`.
    for entry in &RECORDS {
        assert!(!bytes(entry).starts_with(b"is_"), "{}", name(*entry));
    }
}

/// A fixed linear congruential sequence for reproducible generated inputs.
///
/// When a test panics while a sequence is alive, the sequence reports its
/// seed and how many values it produced, which identify the generated case
/// that failed.
struct Sequence {
    seed: u64,
    state: u64,
    drawn: u64,
}

impl Sequence {
    fn new(seed: u64) -> Self {
        Self {
            seed,
            state: seed,
            drawn: 0,
        }
    }

    /// The next value, uniformly in `low..=high` up to the generator's bias.
    fn next_in(&mut self, low: i64, high: i64) -> i64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.drawn += 1;
        let span = (high - low + 1) as u64;
        low + ((self.state >> 33) % span) as i64
    }

    /// An index below `len`, which must be positive.
    fn index(&mut self, len: usize) -> usize {
        self.next_in(0, len as i64 - 1) as usize
    }

    /// One of `items`, which must not be empty.
    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.index(items.len())]
    }
}

impl Drop for Sequence {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "generated inputs: seed {:#x}, failure after {} values were drawn",
                self.seed, self.drawn
            );
        }
    }
}

/// Runs one generated case; if it panics, reports `label`, the input that
/// reproduces the case, before the panic continues.
fn case(label: impl std::fmt::Display, check: impl FnOnce()) {
    struct Report<L: std::fmt::Display>(L);

    impl<L: std::fmt::Display> Drop for Report<L> {
        fn drop(&mut self) {
            if std::thread::panicking() {
                eprintln!("generated case failed: {}", self.0);
            }
        }
    }

    let _report = Report(label);
    check();
}

/// The registered names, the fixed non-names, the special forms and the
/// reserved words, and generated identifiers: edits of registered names and
/// random names.
fn corpus() -> Vec<String> {
    let mut names: Vec<String> = KEYS.iter().map(|k| k.1.to_owned()).collect();
    names.extend(NON_NAMES.iter().map(|s| (*s).to_owned()));
    names.extend(SPECIAL_FORMS.iter().map(|s| (*s).to_owned()));
    names.extend(RESERVED.iter().map(|s| (*s).to_owned()));
    let letters = b"abcegilnopqrstxABCLSZ";
    let tail = b"abcegilnopqrstx_029";
    let mut sequence = Sequence::new(0x5eed_f00d_0001);
    for _ in 0..400 {
        let mut s = KEYS[sequence.index(KEYS.len())].1.as_bytes().to_vec();
        let at = sequence.index(s.len() + 1);
        match sequence.index(4) {
            0 if at < s.len() => {
                s.remove(at);
            }
            1 => s.insert(at, *sequence.pick(tail)),
            2 if at < s.len() => s[at] = *sequence.pick(tail),
            _ if at < s.len() => s[at] = s[at].to_ascii_uppercase(),
            _ => s.push(*sequence.pick(tail)),
        }
        names.push(String::from_utf8(s).unwrap());
    }
    for _ in 0..400 {
        let length = sequence.index(7);
        let mut s = vec![*sequence.pick(letters)];
        for _ in 0..length {
            s.push(*sequence.pick(tail));
        }
        names.push(String::from_utf8(s).unwrap());
    }
    names
}

#[test]
fn lookup_agrees_with_the_keys_on_a_name_corpus() {
    for name in corpus() {
        case(format!("{name:?}"), || {
            let expected = KEYS.iter().find(|key| key.1 == name).map(|key| key.0);
            let found = lookup(name.as_bytes());
            assert_eq!(found, expected, "{name:?}");
            assert_eq!(
                found.map(|id| record(id).arity == 2),
                expected.map(|_| name == "rootn"),
                "{name:?}"
            );
            let span = Span::new(1, 1 + name.len());
            match expected {
                Some(id) => assert_eq!(resolve(name.as_bytes(), span).ok(), Some(id)),
                None => {
                    let error = resolve(name.as_bytes(), span).unwrap_err();
                    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
                    assert_eq!(error.span(), span);
                }
            }
        });
    }
}

#[test]
fn log_value_on_the_cut_is_not_from_below() {
    // The record of `log` holds its value on the cut, the limit from above,
    // the side reached counterclockwise: $\ln \lvert u \rvert + \pi i$ at a
    // negative real $u$, so $\log(-1) = \pi i$, and not
    // $\ln \lvert u \rvert - \pi i$, the limit from below.
    let log = items(FunctionId::Log);
    assert_eq!(log.cut, FunctionCut::Logarithm);
    assert_eq!(log.closed_side, FunctionClosedSide::Above);
    assert_eq!(log.cut_value, FunctionCutValue::Logarithm);
    assert_eq!(imaginary_at_minus_one(log.cut_value), Some((1, 1)));
    assert_ne!(imaginary_at_minus_one(log.cut_value), Some((-1, 1)));
    // The principal range holds the imaginary part $\pi$, not $-\pi$.
    assert_eq!(log.principal_range, FunctionRange::LogarithmStrip);
    // Every record with a cut takes its value on the cut from above, and a
    // record without a cut has neither a side nor a value on a cut.
    for (id, key, _) in KEYS {
        let items = items(id);
        let cut = items.cut != FunctionCut::NoCut;
        assert_eq!(items.closed_side == FunctionClosedSide::Above, cut, "{key}");
        assert_eq!(
            items.closed_side == FunctionClosedSide::NoCut,
            !cut,
            "{key}"
        );
        assert_eq!(items.cut_value == FunctionCutValue::NoCut, !cut, "{key}");
    }
}

/// The imaginary part of the value on the cut at $u = -1$ that `value`
/// gives, as the variant documents it, written as the multiple $p/q$ of
/// $\pi$, or `None` where it is not a rational multiple of $\pi$ at every
/// degree.
fn imaginary_at_minus_one(value: FunctionCutValue) -> Option<(i64, i64)> {
    match value {
        // $\ln 1 + \pi i$.
        FunctionCutValue::Logarithm => Some((1, 1)),
        // $e^{i \pi / n}$, whose imaginary part is $\sin(\pi / n)$.
        FunctionCutValue::Root => None,
        FunctionCutValue::Empty | FunctionCutValue::NoCut => None,
    }
}

#[test]
fn exp_log_keeps_the_domain_of_its_left_side() {
    // $\exp(\log u)$ is undefined at $u = 0$, and $u$ is defined everywhere,
    // so the entry keeps the domain $u \ne 0$ of its left side: it is not
    // unconditional, which the call constructor would apply.
    let entry = identity(FunctionIdentityId::ExpLog);
    assert_eq!(entry.class, FunctionIdentityClass::KeepsLeftDomain);
    assert_ne!(entry.class, FunctionIdentityClass::Unconditional);
    assert_eq!(entry.condition, FunctionIdentityCondition::Nonzero);
    assert_eq!(
        entry.records[..entry.count],
        [FunctionId::Exp, FunctionId::Log]
    );
    // The condition is the domain of `log`, the inner call of the left side.
    assert_eq!(items(FunctionId::Log).domain, FunctionDomain::Nonzero);
    // $\log(\exp u) = u$ holds under the assumption on the imaginary part,
    // and is not unconditional either.
    let reverse = identity(FunctionIdentityId::LogExp);
    assert_eq!(reverse.class, FunctionIdentityClass::UnderAssumption);
    assert_eq!(reverse.condition, FunctionIdentityCondition::PrincipalStrip);
}

#[test]
fn abs_is_not_analytic() {
    assert_eq!(
        items(FunctionId::Abs).analyticity,
        FunctionAnalyticity::NotAnalytic
    );
    // The field is filled for every record, and `abs` is the only record
    // that is analytic nowhere.
    for (id, key, _) in KEYS {
        let analyticity = items(id).analyticity;
        assert_ne!(analyticity, FunctionAnalyticity::Empty, "{key}");
        assert_eq!(
            analyticity == FunctionAnalyticity::NotAnalytic,
            id == FunctionId::Abs,
            "{key}"
        );
    }
}

#[test]
fn unregistered_names_are_not_resolved() {
    // Names that a user might declare, near misses, the empty name and names
    // longer than the capacity of 8 bytes find no record, and the entry
    // reports `Syntax` with the span that its caller gives: there is no
    // table of declared functions to fall back on.
    let cases = [
        ("f", Span::new(0, 1)),
        ("g", Span::new(4, 5)),
        ("foo", Span::new(2, 5)),
        ("sinh", Span::new(0, 4)),
        ("Sin", Span::new(7, 10)),
        ("", Span::new(3, 3)),
        ("rootnrootn", Span::new(0, 10)),
        ("sqrtsqrtsqrt", Span::new(5, 17)),
        ("f", None),
    ];
    for (name, span) in cases {
        assert_eq!(lookup(name.as_bytes()), None, "{name:?}");
        let error = resolve(name.as_bytes(), span).unwrap_err();
        assert_eq!(
            error.kind(),
            ErrorKind::Fault(FaultKind::Syntax),
            "{name:?}"
        );
        assert_eq!(error.span(), span, "{name:?}");
    }
}

#[test]
fn lookup_and_record_access_take_no_context() {
    // Each binding fixes the type of a function of the registry; none takes
    // a request context, so none can charge work.
    let find: fn(&[u8]) -> Option<FunctionId> = lookup;
    let entry: fn(&[u8], Option<Span>) -> Result<FunctionId> = resolve;
    let access: fn(FunctionId) -> FunctionRecord = record;
    let slots: fn(FunctionId) -> FunctionItems = items;
    let list: fn(FunctionIdentityId) -> FunctionIdentity = identity;
    assert_eq!(find(b"log"), Some(FunctionId::Log));
    assert_eq!(find(b"ln"), None);
    assert_eq!(entry(b"log", None).ok(), Some(FunctionId::Log));
    let error = entry(b"ln", Span::new(0, 2)).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Fault(FaultKind::Syntax));
    assert_eq!(access(FunctionId::Log).arity, 1);
    assert_eq!(slots(FunctionId::Log).domain, FunctionDomain::Nonzero);
    assert_eq!(
        list(FunctionIdentityId::ExpLog).records,
        [FunctionId::Exp, FunctionId::Log]
    );
}

/// The domain labels of the contract, in the order of the records.
const DOMAINS: [FunctionDomain; 11] = [
    FunctionDomain::Total,
    FunctionDomain::Total,
    FunctionDomain::CosineNonzero,
    FunctionDomain::RealUnitInterval,
    FunctionDomain::RealUnitInterval,
    FunctionDomain::Real,
    FunctionDomain::Total,
    FunctionDomain::Nonzero,
    FunctionDomain::Total,
    FunctionDomain::PositiveDegree,
    FunctionDomain::Total,
];

/// The supports of the contract.
const SUPPORTS: [FunctionSupport; 11] = [
    FunctionSupport::Complex,
    FunctionSupport::Complex,
    FunctionSupport::Complex,
    FunctionSupport::Real,
    FunctionSupport::Real,
    FunctionSupport::Real,
    FunctionSupport::Complex,
    FunctionSupport::Complex,
    FunctionSupport::Complex,
    FunctionSupport::Complex,
    FunctionSupport::Complex,
];

/// The cuts of the contract.
const CUTS: [FunctionCut; 11] = [
    FunctionCut::NoCut,
    FunctionCut::NoCut,
    FunctionCut::NoCut,
    FunctionCut::NoCut,
    FunctionCut::NoCut,
    FunctionCut::NoCut,
    FunctionCut::NoCut,
    FunctionCut::Logarithm,
    FunctionCut::Root,
    FunctionCut::RootFromDegreeTwo,
    FunctionCut::NoCut,
];

/// The closed sides of the contract.
const SIDES: [FunctionClosedSide; 11] = [
    FunctionClosedSide::NoCut,
    FunctionClosedSide::NoCut,
    FunctionClosedSide::NoCut,
    FunctionClosedSide::NoCut,
    FunctionClosedSide::NoCut,
    FunctionClosedSide::NoCut,
    FunctionClosedSide::NoCut,
    FunctionClosedSide::Above,
    FunctionClosedSide::Above,
    FunctionClosedSide::Above,
    FunctionClosedSide::NoCut,
];

/// The values on the cut of the contract.
const CUT_VALUES: [FunctionCutValue; 11] = [
    FunctionCutValue::NoCut,
    FunctionCutValue::NoCut,
    FunctionCutValue::NoCut,
    FunctionCutValue::NoCut,
    FunctionCutValue::NoCut,
    FunctionCutValue::NoCut,
    FunctionCutValue::NoCut,
    FunctionCutValue::Logarithm,
    FunctionCutValue::Root,
    FunctionCutValue::Root,
    FunctionCutValue::NoCut,
];

/// The principal ranges of the contract.
const RANGES: [FunctionRange; 11] = [
    FunctionRange::SingleValued,
    FunctionRange::SingleValued,
    FunctionRange::SingleValued,
    FunctionRange::ClosedHalfPi,
    FunctionRange::ZeroToPi,
    FunctionRange::OpenHalfPi,
    FunctionRange::SingleValued,
    FunctionRange::LogarithmStrip,
    FunctionRange::RootArgument,
    FunctionRange::RootArgument,
    FunctionRange::SingleValued,
];

/// The values at 0, 1, $-1$ and $i$ of the contract.
const POINT_VALUES: [[FunctionPointValue; 4]; 11] = [
    [
        FunctionPointValue::Zero,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::One,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::Zero,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::ZeroPi,
        FunctionPointValue::HalfPi,
        FunctionPointValue::MinusHalfPi,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::HalfPi,
        FunctionPointValue::ZeroPi,
        FunctionPointValue::Pi,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::ZeroPi,
        FunctionPointValue::QuarterPi,
        FunctionPointValue::MinusQuarterPi,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::One,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::NoValue,
        FunctionPointValue::Zero,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::Argument,
        FunctionPointValue::Argument,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::Argument,
        FunctionPointValue::Argument,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
    ],
    [
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
        FunctionPointValue::NoValue,
        FunctionPointValue::One,
    ],
];

/// The value families of the contract.
const FAMILIES: [FunctionFamily; 11] = [
    FunctionFamily::QuarterTurns,
    FunctionFamily::QuarterTurns,
    FunctionFamily::QuarterTurns,
    FunctionFamily::NoFamily,
    FunctionFamily::NoFamily,
    FunctionFamily::NoFamily,
    FunctionFamily::NoFamily,
    FunctionFamily::NoFamily,
    FunctionFamily::PrincipalRoots,
    FunctionFamily::PrincipalRoots,
    FunctionFamily::Modulus,
];

/// The quarter-turn tables of `sin`, `cos` and `tan` in the contract; every
/// other record has `NoQuarterTurns` at each quarter turn.
const TURNS: [(FunctionId, [FunctionQuarterValue; 4]); 3] = [
    (
        FunctionId::Sin,
        [
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::One,
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::MinusOne,
        ],
    ),
    (
        FunctionId::Cos,
        [
            FunctionQuarterValue::One,
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::MinusOne,
            FunctionQuarterValue::Zero,
        ],
    ),
    (
        FunctionId::Tan,
        [
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::Undefined,
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::Undefined,
        ],
    ),
];

/// The undefined points of the contract.
const UNDEFINED: [FunctionUndefinedPoints; 11] = [
    FunctionUndefinedPoints::NoPoints,
    FunctionUndefinedPoints::NoPoints,
    FunctionUndefinedPoints::OddHalfPiMultiples,
    FunctionUndefinedPoints::BeyondOneOrImaginary,
    FunctionUndefinedPoints::BeyondOneOrImaginary,
    FunctionUndefinedPoints::ImaginaryMultiples,
    FunctionUndefinedPoints::NoPoints,
    FunctionUndefinedPoints::Zero,
    FunctionUndefinedPoints::NoPoints,
    FunctionUndefinedPoints::ExcludedDegrees,
    FunctionUndefinedPoints::NoPoints,
];

/// The periods of the contract.
const PERIODS: [FunctionPeriod; 11] = [
    FunctionPeriod::TwoPi,
    FunctionPeriod::TwoPi,
    FunctionPeriod::Pi,
    FunctionPeriod::NoPeriod,
    FunctionPeriod::NoPeriod,
    FunctionPeriod::NoPeriod,
    FunctionPeriod::TwoPiI,
    FunctionPeriod::NoPeriod,
    FunctionPeriod::NoPeriod,
    FunctionPeriod::NoPeriod,
    FunctionPeriod::NoPeriod,
];

/// The parities of the contract.
const PARITIES: [FunctionParity; 11] = [
    FunctionParity::Odd,
    FunctionParity::Even,
    FunctionParity::Odd,
    FunctionParity::Odd,
    FunctionParity::Reflection,
    FunctionParity::Odd,
    FunctionParity::NoParity,
    FunctionParity::NoParity,
    FunctionParity::NoParity,
    FunctionParity::NoParity,
    FunctionParity::Even,
];

/// The sign rules of the contract.
const SIGN_RULES: [FunctionSignRule; 11] = [
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::NoSignRule,
    FunctionSignRule::Modulus,
];

/// The conjugate symmetries of the contract.
const CONJUGATIONS: [FunctionConjugation; 11] = [
    FunctionConjugation::OnDomain,
    FunctionConjugation::OnDomain,
    FunctionConjugation::OnDomain,
    FunctionConjugation::OnDomain,
    FunctionConjugation::OnDomain,
    FunctionConjugation::OnDomain,
    FunctionConjugation::OnDomain,
    FunctionConjugation::OffCut,
    FunctionConjugation::OffCut,
    FunctionConjugation::OffCut,
    FunctionConjugation::OnDomain,
];

/// The zeros and poles of the contract.
const ZEROS: [FunctionZerosAndPoles; 11] = [
    FunctionZerosAndPoles::MultiplesOfPi,
    FunctionZerosAndPoles::OddHalfPiMultiples,
    FunctionZerosAndPoles::TangentZerosAndPoles,
    FunctionZerosAndPoles::ZeroAtOrigin,
    FunctionZerosAndPoles::ZeroAtOne,
    FunctionZerosAndPoles::ZeroAtOrigin,
    FunctionZerosAndPoles::NoZeros,
    FunctionZerosAndPoles::ZeroAtOne,
    FunctionZerosAndPoles::ZeroAtOrigin,
    FunctionZerosAndPoles::ZeroAtOrigin,
    FunctionZerosAndPoles::ZeroAtOrigin,
];

/// The derivative formulas and regions of the contract.
const DERIVATIVES: [(FunctionDerivative, FunctionRegion); 11] = [
    (FunctionDerivative::Cosine, FunctionRegion::Domain),
    (FunctionDerivative::NegativeSine, FunctionRegion::Domain),
    (
        FunctionDerivative::InverseCosineSquared,
        FunctionRegion::Domain,
    ),
    (
        FunctionDerivative::Arcsine,
        FunctionRegion::RealOpenUnitInterval,
    ),
    (
        FunctionDerivative::Arccosine,
        FunctionRegion::RealOpenUnitInterval,
    ),
    (FunctionDerivative::Arctangent, FunctionRegion::RealLine),
    (FunctionDerivative::Itself, FunctionRegion::Domain),
    (
        FunctionDerivative::Reciprocal,
        FunctionRegion::OffCutOrRealDomain,
    ),
    (
        FunctionDerivative::RootPower,
        FunctionRegion::OffCutOrRealNonzero,
    ),
    (
        FunctionDerivative::RootPower,
        FunctionRegion::OffCutOrRealNonzero,
    ),
    (FunctionDerivative::Sign, FunctionRegion::RealNonzero),
];

/// The regular-point methods of the contract; `asin`, `acos` and `atan`
/// have none yet.
const EXPANSIONS: [FunctionExpansion; 11] = [
    FunctionExpansion::SineRecurrence,
    FunctionExpansion::CosineRecurrence,
    FunctionExpansion::TangentQuotient,
    FunctionExpansion::Empty,
    FunctionExpansion::Empty,
    FunctionExpansion::Empty,
    FunctionExpansion::ExponentialRecurrence,
    FunctionExpansion::LogarithmIntegral,
    FunctionExpansion::RootComposition,
    FunctionExpansion::RootComposition,
    FunctionExpansion::ModulusSign,
];

/// The analyticity of the contract.
const ANALYTICITY: [FunctionAnalyticity; 11] = [
    FunctionAnalyticity::Entire,
    FunctionAnalyticity::Entire,
    FunctionAnalyticity::Meromorphic,
    FunctionAnalyticity::RealAnalyticOnOpenUnitInterval,
    FunctionAnalyticity::RealAnalyticOnOpenUnitInterval,
    FunctionAnalyticity::RealAnalyticOnReals,
    FunctionAnalyticity::Entire,
    FunctionAnalyticity::OffCut,
    FunctionAnalyticity::OffCut,
    FunctionAnalyticity::OffCut,
    FunctionAnalyticity::NotAnalytic,
];

/// The property inference of the contract.
const INFERENCES: [FunctionInference; 11] = [
    FunctionInference::RealOnReals,
    FunctionInference::RealOnReals,
    FunctionInference::RealOnReals,
    FunctionInference::RealValued,
    FunctionInference::RealValued,
    FunctionInference::RealValued,
    FunctionInference::Exponential,
    FunctionInference::Logarithm,
    FunctionInference::Root,
    FunctionInference::Root,
    FunctionInference::Modulus,
];

/// The number of records whose slot `empty` does not hold the empty variant.
fn filled(empty: fn(&FunctionItems) -> bool) -> usize {
    KEYS.iter().filter(|key| !empty(&items(key.0))).count()
}

#[test]
fn items_are_those_of_the_contract() {
    for (index, (id, key, _)) in KEYS.into_iter().enumerate() {
        let items = items(id);
        assert_eq!(items.domain, DOMAINS[index], "{key}");
        assert_eq!(items.support, SUPPORTS[index], "{key}");
        assert_eq!(items.cut, CUTS[index], "{key}");
        assert_eq!(items.closed_side, SIDES[index], "{key}");
        assert_eq!(items.cut_value, CUT_VALUES[index], "{key}");
        assert_eq!(items.principal_range, RANGES[index], "{key}");
        let points = [
            items.at_zero,
            items.at_one,
            items.at_minus_one,
            items.at_unit,
        ];
        assert_eq!(points, POINT_VALUES[index], "{key}");
        assert_eq!(items.family, FAMILIES[index], "{key}");
        let turns = TURNS
            .iter()
            .find(|turns| turns.0 == id)
            .map_or([FunctionQuarterValue::NoQuarterTurns; 4], |turns| turns.1);
        assert_eq!(items.quarter_turns, turns, "{key}");
        assert_eq!(items.undefined_points, UNDEFINED[index], "{key}");
        assert_eq!(items.period, PERIODS[index], "{key}");
        assert_eq!(items.parity, PARITIES[index], "{key}");
        assert_eq!(items.sign_rule, SIGN_RULES[index], "{key}");
        assert_eq!(items.conjugation, CONJUGATIONS[index], "{key}");
        assert_eq!(items.zeros_and_poles, ZEROS[index], "{key}");
        let derivative = (items.derivative, items.region);
        assert_eq!(derivative, DERIVATIVES[index], "{key}");
        assert_eq!(items.expansion, EXPANSIONS[index], "{key}");
        let pole = match id {
            FunctionId::Tan => FunctionPoleExpansion::TangentQuotient,
            _ => FunctionPoleExpansion::NoPoles,
        };
        assert_eq!(items.pole_expansion, pole, "{key}");
        assert_eq!(items.analyticity, ANALYTICITY[index], "{key}");
        assert_eq!(items.inference, INFERENCES[index], "{key}");
        // The 15 slots of the exemption list are empty.
        assert_eq!(items.branch_expansion, FunctionBranchExpansion::Empty);
        assert_eq!(items.at_plus_infinity, FunctionAtInfinity::Empty);
        assert_eq!(items.at_minus_infinity, FunctionAtInfinity::Empty);
        assert_eq!(items.kernel, FunctionKernel::Empty);
        assert_eq!(items.requirement, FunctionRequirement::Empty);
        assert_eq!(items.taylor_model, FunctionTaylorModel::Empty);
        assert_eq!(items.binary64, FunctionBinary64::Empty);
        assert_eq!(items.antiderivative, FunctionAntiderivative::Empty);
        assert_eq!(items.integration_result, FunctionIntegrationResult::Empty);
        assert_eq!(items.derivative_family, FunctionDerivativeFamily::Empty);
        assert_eq!(items.summation, FunctionSummation::Empty);
        assert_eq!(items.inversion, FunctionInversion::Empty);
        assert_eq!(items.limit_rule, FunctionLimitRule::Empty);
        assert_eq!(items.output_name, FunctionOutputName::Empty);
        assert_eq!(items.dimensions, FunctionDimensions::Empty);
    }
    // The 24 filled slots: 23 hold a value for each of the 11 records, and
    // the regular-point method for 8, without `asin`, `acos` and `atan`.
    let counts = [
        filled(|i| i.domain == FunctionDomain::Empty),
        filled(|i| i.support == FunctionSupport::Empty),
        filled(|i| i.cut == FunctionCut::Empty),
        filled(|i| i.closed_side == FunctionClosedSide::Empty),
        filled(|i| i.cut_value == FunctionCutValue::Empty),
        filled(|i| i.principal_range == FunctionRange::Empty),
        filled(|i| i.at_zero == FunctionPointValue::Empty),
        filled(|i| i.at_one == FunctionPointValue::Empty),
        filled(|i| i.at_minus_one == FunctionPointValue::Empty),
        filled(|i| i.at_unit == FunctionPointValue::Empty),
        filled(|i| i.family == FunctionFamily::Empty),
        filled(|i| i.quarter_turns.contains(&FunctionQuarterValue::Empty)),
        filled(|i| i.undefined_points == FunctionUndefinedPoints::Empty),
        filled(|i| i.period == FunctionPeriod::Empty),
        filled(|i| i.parity == FunctionParity::Empty),
        filled(|i| i.sign_rule == FunctionSignRule::Empty),
        filled(|i| i.conjugation == FunctionConjugation::Empty),
        filled(|i| i.zeros_and_poles == FunctionZerosAndPoles::Empty),
        filled(|i| i.derivative == FunctionDerivative::Empty),
        filled(|i| i.region == FunctionRegion::Empty),
        filled(|i| i.pole_expansion == FunctionPoleExpansion::Empty),
        filled(|i| i.analyticity == FunctionAnalyticity::Empty),
        filled(|i| i.inference == FunctionInference::Empty),
    ];
    assert_eq!(counts, [11; 23]);
    assert_eq!(filled(|i| i.expansion == FunctionExpansion::Empty), 8);
    for id in [FunctionId::Asin, FunctionId::Acos, FunctionId::Atan] {
        assert_eq!(items(id).expansion, FunctionExpansion::Empty, "{id:?}");
    }
}

/// The identity list of the contract: each entry with its class, its
/// condition and the records it names.
const IDENTITY_LIST: [(
    FunctionIdentityId,
    FunctionIdentityClass,
    FunctionIdentityCondition,
    &[FunctionId],
); 10] = [
    (
        FunctionIdentityId::SqrtEqRootn,
        FunctionIdentityClass::Unconditional,
        FunctionIdentityCondition::NoCondition,
        &[FunctionId::Sqrt, FunctionId::Rootn],
    ),
    (
        FunctionIdentityId::RootnOne,
        FunctionIdentityClass::Unconditional,
        FunctionIdentityCondition::NoCondition,
        &[FunctionId::Rootn],
    ),
    (
        FunctionIdentityId::AbsAbs,
        FunctionIdentityClass::Unconditional,
        FunctionIdentityCondition::NoCondition,
        &[FunctionId::Abs],
    ),
    (
        FunctionIdentityId::RootPow,
        FunctionIdentityClass::Unconditional,
        FunctionIdentityCondition::NoCondition,
        &[FunctionId::Sqrt, FunctionId::Rootn],
    ),
    (
        FunctionIdentityId::SqrtSq,
        FunctionIdentityClass::UnderAssumption,
        FunctionIdentityCondition::Real,
        &[FunctionId::Sqrt, FunctionId::Abs],
    ),
    (
        FunctionIdentityId::LogExp,
        FunctionIdentityClass::UnderAssumption,
        FunctionIdentityCondition::PrincipalStrip,
        &[FunctionId::Log, FunctionId::Exp],
    ),
    (
        FunctionIdentityId::ExpLog,
        FunctionIdentityClass::KeepsLeftDomain,
        FunctionIdentityCondition::Nonzero,
        &[FunctionId::Exp, FunctionId::Log],
    ),
    (
        FunctionIdentityId::SinAsin,
        FunctionIdentityClass::KeepsLeftDomain,
        FunctionIdentityCondition::RealUnitInterval,
        &[FunctionId::Sin, FunctionId::Asin],
    ),
    (
        FunctionIdentityId::CosAcos,
        FunctionIdentityClass::KeepsLeftDomain,
        FunctionIdentityCondition::RealUnitInterval,
        &[FunctionId::Cos, FunctionId::Acos],
    ),
    (
        FunctionIdentityId::TanAtan,
        FunctionIdentityClass::KeepsLeftDomain,
        FunctionIdentityCondition::Real,
        &[FunctionId::Tan, FunctionId::Atan],
    ),
];

#[test]
fn identities_are_those_of_the_contract() {
    assert_eq!(IDENTITIES.len(), IDENTITY_LIST.len());
    for (index, (id, class, condition, records)) in IDENTITY_LIST.into_iter().enumerate() {
        let entry = identity(id);
        assert_eq!(entry, IDENTITIES[index], "{id:?}");
        assert_eq!(entry.id, id);
        assert_eq!(entry.class, class, "{id:?}");
        assert_eq!(entry.condition, condition, "{id:?}");
        assert!((1..=entry.records.len()).contains(&entry.count), "{id:?}");
        assert_eq!(entry.records[..entry.count], *records, "{id:?}");
        // The unused positions repeat the first record.
        assert!(
            entry.records[entry.count..]
                .iter()
                .all(|r| *r == entry.records[0]),
            "{id:?}"
        );
        // Only an entry with a condition is of a class other than
        // unconditional.
        assert_eq!(
            class == FunctionIdentityClass::Unconditional,
            condition == FunctionIdentityCondition::NoCondition,
            "{id:?}"
        );
    }
    // Every record is named by at least one entry.
    for (id, key, _) in KEYS {
        let named = IDENTITIES
            .iter()
            .any(|entry| entry.records[..entry.count].contains(&id));
        assert!(named, "{key}");
    }
}

/// Tests of the item slots that read one record against another or against
/// the documented meaning of a variant.
mod items {
    use super::*;

    #[test]
    fn items_follow_the_records() {
        for (id, key, _) in KEYS {
            assert_eq!(items(id), ITEMS[id as usize], "{key}");
            // The quarter-turn values are filled exactly for that family.
            let filled = items(id)
                .quarter_turns
                .iter()
                .filter(|v| **v != FunctionQuarterValue::NoQuarterTurns)
                .count();
            match items(id).family {
                FunctionFamily::QuarterTurns => assert_eq!(filled, 4, "{key}"),
                FunctionFamily::Empty
                | FunctionFamily::NoFamily
                | FunctionFamily::PrincipalRoots
                | FunctionFamily::Modulus => assert_eq!(filled, 0, "{key}"),
            }
        }
    }

    /// The exact points of the value slots.
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Point {
        Zero,
        One,
        MinusOne,
        Unit,
    }

    impl Point {
        const ALL: [Point; 4] = [Point::Zero, Point::One, Point::MinusOne, Point::Unit];

        fn slot(self, items: FunctionItems) -> FunctionPointValue {
            match self {
                Point::Zero => items.at_zero,
                Point::One => items.at_one,
                Point::MinusOne => items.at_minus_one,
                Point::Unit => items.at_unit,
            }
        }
    }

    /// The registered special values of the contract: $\sin 0$, $\cos 0$,
    /// $\tan 0$, $\exp 0$, $\log 1$, `asin`, `acos` and `atan` at $-1$, 0
    /// and 1, `sqrt` and `rootn` at 0 and 1, and $\lvert i \rvert$.
    const VALUES: [(FunctionId, Point); 19] = [
        (FunctionId::Sin, Point::Zero),
        (FunctionId::Cos, Point::Zero),
        (FunctionId::Tan, Point::Zero),
        (FunctionId::Exp, Point::Zero),
        (FunctionId::Log, Point::One),
        (FunctionId::Asin, Point::MinusOne),
        (FunctionId::Asin, Point::Zero),
        (FunctionId::Asin, Point::One),
        (FunctionId::Acos, Point::MinusOne),
        (FunctionId::Acos, Point::Zero),
        (FunctionId::Acos, Point::One),
        (FunctionId::Atan, Point::MinusOne),
        (FunctionId::Atan, Point::Zero),
        (FunctionId::Atan, Point::One),
        (FunctionId::Sqrt, Point::Zero),
        (FunctionId::Sqrt, Point::One),
        (FunctionId::Rootn, Point::Zero),
        (FunctionId::Rootn, Point::One),
        (FunctionId::Abs, Point::Unit),
    ];

    /// How a registered value is built.
    #[derive(Debug, PartialEq)]
    enum Form {
        /// An integer.
        Integer,
        /// The argument itself.
        Argument,
        /// The product of a rational and $\pi$.
        PiMultiple,
    }

    /// The form in which `value` is built, as the variant documents it.
    fn form(value: FunctionPointValue) -> Option<Form> {
        match value {
            FunctionPointValue::Empty | FunctionPointValue::NoValue => None,
            FunctionPointValue::Zero | FunctionPointValue::One => Some(Form::Integer),
            FunctionPointValue::Argument => Some(Form::Argument),
            FunctionPointValue::ZeroPi
            | FunctionPointValue::HalfPi
            | FunctionPointValue::MinusHalfPi
            | FunctionPointValue::Pi
            | FunctionPointValue::QuarterPi
            | FunctionPointValue::MinusQuarterPi => Some(Form::PiMultiple),
        }
    }

    #[test]
    fn values_are_built_in_the_form_of_their_record() {
        // The contract fixes the form in which the call constructor builds a
        // value, which decides the nodes that it builds and so the work of a
        // call: the inverse trigonometric functions write every value as a
        // multiple of $\pi$, 0 as $0 \pi$; the roots return their argument
        // at their fixed points 0 and 1; the other records build an integer.
        for (id, point) in VALUES {
            let expected = match id {
                FunctionId::Asin | FunctionId::Acos | FunctionId::Atan => Form::PiMultiple,
                FunctionId::Sqrt | FunctionId::Rootn => Form::Argument,
                _ => Form::Integer,
            };
            assert_eq!(
                form(point.slot(items(id))),
                Some(expected),
                "{id:?} at {point:?}"
            );
        }
        // Every other point has no registered value.
        for (id, key, _) in KEYS {
            for point in Point::ALL {
                let registered = VALUES.contains(&(id, point));
                assert_eq!(
                    form(point.slot(items(id))).is_some(),
                    registered,
                    "{key} at {point:?}"
                );
            }
        }
    }

    /// The domain label that `domain` gives at the degree `degree`: a degree
    /// that is a positive integer meets `PositiveDegree` for every operand.
    fn domain_at(domain: FunctionDomain, degree: u32) -> FunctionDomain {
        match domain {
            FunctionDomain::PositiveDegree if degree >= 1 => FunctionDomain::Total,
            other => other,
        }
    }

    /// The cut that `cut` gives at the degree `degree`.
    fn cut_at(cut: FunctionCut, degree: u32) -> FunctionCut {
        match cut {
            FunctionCut::RootFromDegreeTwo if degree >= 2 => FunctionCut::Root,
            FunctionCut::RootFromDegreeTwo => FunctionCut::NoCut,
            other => other,
        }
    }

    /// The undefined points that `points` gives at the degree `degree`: a
    /// degree that is a positive integer is not excluded, and the operand
    /// has no undefined point.
    fn undefined_at(points: FunctionUndefinedPoints, degree: u32) -> FunctionUndefinedPoints {
        match points {
            FunctionUndefinedPoints::ExcludedDegrees if degree >= 1 => {
                FunctionUndefinedPoints::NoPoints
            }
            other => other,
        }
    }

    /// The items of a record at the degree `degree`.
    fn at_degree(items: FunctionItems, degree: u32) -> FunctionItems {
        FunctionItems {
            domain: domain_at(items.domain, degree),
            cut: cut_at(items.cut, degree),
            undefined_points: undefined_at(items.undefined_points, degree),
            ..items
        }
    }

    #[test]
    fn sqrt_has_the_items_of_rootn_of_degree_two() {
        // `sqrt_eq_rootn`: every slot means the same for `sqrt` and for
        // `rootn` of degree 2. The three slots that depend on the degree are
        // compared at degree 2 through the labels that they give there; the
        // other 36 slots are equal.
        let (sqrt, rootn) = (items(FunctionId::Sqrt), items(FunctionId::Rootn));
        assert_eq!(at_degree(sqrt, 2), sqrt);
        assert_eq!(at_degree(rootn, 2), sqrt);
        for point in Point::ALL {
            assert_eq!(point.slot(sqrt), point.slot(rootn), "{point:?}");
        }
        // At degree 1 the root has no cut and is not `sqrt`.
        assert_eq!(cut_at(rootn.cut, 1), FunctionCut::NoCut);
        assert_ne!(at_degree(rootn, 1), sqrt);
    }

    #[test]
    fn only_the_sign_formula_has_the_real_nonzero_region() {
        // The region `RealNonzero` adds no condition; the case split of the
        // `Sign` formula is what keeps the derivative at 0 formal. A record
        // therefore has that region exactly when it has that formula.
        for (id, key, _) in KEYS {
            let items = items(id);
            assert_eq!(
                items.region == FunctionRegion::RealNonzero,
                items.derivative == FunctionDerivative::Sign,
                "{key}"
            );
        }
    }
}
