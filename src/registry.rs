//! The function registry: one static record for each of the eleven
//! functions of function expressions, `sin`, `cos`, `tan`, `asin`, `acos`,
//! `atan`, `exp`, `log`, `sqrt`, `rootn` and `abs`, and the identity list,
//! which relates calls of several of them or nested calls.
//!
//! A record has two parts, kept in two static tables in the order of the
//! records. `RECORDS` holds the identity fields: the identifier, the name,
//! the arity and the argument roles. `ITEMS` holds the 39 slots of the
//! record schema, one field each: the node, the domain and the branch cuts;
//! the special values and symmetries; the derivatives; the series; numerical
//! evaluation; the connection rules; and the other fields. Every slot is a
//! fieldless enumeration or an array of them, a template that its reader
//! interprets with an exhaustive `match`. Every slot enumeration has the
//! variant `Empty`, which only the slots of the exemption list and the
//! regular-point method of `asin`, `acos` and `atan` hold; a value such as
//! `NoValue` or `NoCut` is an ordinary value of its slot. `IDENTITIES`
//! holds the ten entries of the identity list.
//!
//! The module is written to be proved, in the shapes of the qualification
//! cases `registry-records` and `registry-items`: the records are plain
//! data, names are zero-padded byte arrays with a length, lookup is an index
//! loop that compares the bytes in a helper, and access from an identifier
//! is an exhaustive `match` that returns a copy. It depends on no term,
//! request context or formatting, and lookup and access charge no work. The
//! contract of the component, `docs/components/registry/contract.md`, states
//! the meaning of every slot and of every entry.

#![cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the registry has no production caller yet; its unit tests read every record"
    )
)]

use crate::{Error, FaultKind, Result, Span};

/// The identifier of a registered function: one variant per name, in the
/// order of the records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionId {
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Exp,
    Log,
    Sqrt,
    Rootn,
    Abs,
}

/// The role of an argument position.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionRole {
    /// The operand $u$: a complex argument.
    Operand,
    /// The degree $n$ of `rootn`: an ordinary value argument, like the
    /// operand. The call is defined only where its value is a positive
    /// integer, as the domain label `PositiveDegree` states.
    Degree,
}

/// The identity fields of a registered function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FunctionRecord {
    pub(crate) id: FunctionId,
    /// The name in the first `length` bytes, followed by zero bytes.
    pub(crate) name: [u8; 8],
    pub(crate) length: usize,
    /// The number of arguments of a call.
    pub(crate) arity: usize,
    /// The role of each argument position. The positions from `arity` on are
    /// unused and hold `Operand`.
    pub(crate) roles: [FunctionRole; 2],
}

/// The records, in the order of the identifiers.
static RECORDS: [FunctionRecord; 11] = [
    FunctionRecord {
        id: FunctionId::Sin,
        name: *b"sin\0\0\0\0\0",
        length: 3,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Cos,
        name: *b"cos\0\0\0\0\0",
        length: 3,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Tan,
        name: *b"tan\0\0\0\0\0",
        length: 3,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Asin,
        name: *b"asin\0\0\0\0",
        length: 4,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Acos,
        name: *b"acos\0\0\0\0",
        length: 4,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Atan,
        name: *b"atan\0\0\0\0",
        length: 4,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Exp,
        name: *b"exp\0\0\0\0\0",
        length: 3,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Log,
        name: *b"log\0\0\0\0\0",
        length: 3,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Sqrt,
        name: *b"sqrt\0\0\0\0",
        length: 4,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
    FunctionRecord {
        id: FunctionId::Rootn,
        name: *b"rootn\0\0\0",
        length: 5,
        arity: 2,
        roles: [FunctionRole::Operand, FunctionRole::Degree],
    },
    FunctionRecord {
        id: FunctionId::Abs,
        name: *b"abs\0\0\0\0\0",
        length: 3,
        arity: 1,
        roles: [FunctionRole::Operand, FunctionRole::Operand],
    },
];

/// Whether the record is named `name`, compared byte by byte.
fn named(record: &FunctionRecord, name: &[u8]) -> bool {
    if record.length != name.len() {
        return false;
    }
    let mut index = 0;
    while index < record.length {
        if record.name[index] != name[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// The identifier of the record named `name`, or `None` for every other
/// name. The work is bounded by the number of records and the name capacity,
/// 11 records of 8 bytes, so no work is charged and no context is taken.
pub(crate) fn lookup(name: &[u8]) -> Option<FunctionId> {
    let mut index = 0;
    while index < RECORDS.len() {
        if named(&RECORDS[index], name) {
            return Some(RECORDS[index].id);
        }
        index += 1;
    }
    None
}

/// The identifier of the record named `name`. A name that the registry does
/// not hold fails with `Fault(Syntax)` and the span `span` that the caller
/// gives, such as that of the name in the input; there is no other table of
/// functions to look in. Like `lookup`, it charges no work.
pub(crate) fn resolve(name: &[u8], span: Option<Span>) -> Result<FunctionId> {
    match lookup(name) {
        Some(id) => Ok(id),
        None => Err(Error::new(FaultKind::Syntax, span, "unknown function")),
    }
}

/// A copy of the record of `id`.
pub(crate) fn record(id: FunctionId) -> FunctionRecord {
    match id {
        FunctionId::Sin => RECORDS[0],
        FunctionId::Cos => RECORDS[1],
        FunctionId::Tan => RECORDS[2],
        FunctionId::Asin => RECORDS[3],
        FunctionId::Acos => RECORDS[4],
        FunctionId::Atan => RECORDS[5],
        FunctionId::Exp => RECORDS[6],
        FunctionId::Log => RECORDS[7],
        FunctionId::Sqrt => RECORDS[8],
        FunctionId::Rootn => RECORDS[9],
        FunctionId::Abs => RECORDS[10],
    }
}

/// The domain label of a record: the condition on its arguments, the
/// operand $u$ and the degree $n$, under which it has a value. The contract
/// writes each label as a condition of function values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionDomain {
    /// The slot is empty.
    Empty,
    /// Every argument.
    Total,
    /// $\cos u \ne 0$.
    CosineNonzero,
    /// A real $u$ with $-1 \le u \le 1$.
    RealUnitInterval,
    /// A real $u$.
    Real,
    /// $u \ne 0$.
    Nonzero,
    /// Every operand, with a degree $n$ that is an integer and $n \ge 1$.
    PositiveDegree,
}

/// The arguments and values of a record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionSupport {
    /// The slot is empty.
    Empty,
    /// Complex arguments.
    Complex,
    /// Real arguments only, with real values, so the record is continuous
    /// only along real paths.
    Real,
}

/// The branch cut of a record and its sharp part, the points of the domain
/// where the record jumps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionCut {
    /// The slot is empty.
    Empty,
    /// No cut.
    NoCut,
    /// The nonpositive real axis, with jumps on the negative real axis. The
    /// branch point 0 is outside the domain.
    Logarithm,
    /// The nonpositive real axis, with jumps on the negative real axis. The
    /// record is defined and continuous at the branch point 0.
    Root,
    /// `Root` for a degree of at least 2, and no cut for degree 1.
    RootFromDegreeTwo,
}

/// The side from which a record takes its value on its cut, the side
/// reached when circling the branch point counterclockwise. It applies on
/// the cut that the cut slot gives at the degree of the call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionClosedSide {
    /// The slot is empty.
    Empty,
    /// No cut, so no side.
    NoCut,
    /// The record is continuous on its cut from above, the closed upper
    /// half-plane: the side of a cut along the negative real axis.
    Above,
}

/// The value of a record at a point $u$ of its cut, the limit from the
/// closed side. It applies on the cut that the cut slot gives at the degree
/// of the call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionCutValue {
    /// The slot is empty.
    Empty,
    /// No cut, so no value on it.
    NoCut,
    /// $\ln \lvert u \rvert + \pi i$ at a negative real $u$.
    Logarithm,
    /// $\lvert u \rvert^{1/n} e^{i \pi / n}$ at a negative real $u$, for the
    /// degree $n$ of the call, which is 2 for `sqrt`: $i \sqrt{\lvert u \rvert}$.
    Root,
}

/// The principal range of a record: the values of its principal branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionRange {
    /// The slot is empty.
    Empty,
    /// The record is single-valued and has no branch to choose.
    SingleValued,
    /// The real interval $[-\pi/2, \pi/2]$.
    ClosedHalfPi,
    /// The real interval $[0, \pi]$.
    ZeroToPi,
    /// The real interval $(-\pi/2, \pi/2)$.
    OpenHalfPi,
    /// The values $w$ with $-\pi \lt \mathrm{Im}\, w \le \pi$.
    LogarithmStrip,
    /// The value 0 and the values $w \ne 0$ whose argument lies in
    /// $(-\pi/n, \pi/n]$, for the degree $n$ of the call, which is 2 for
    /// `sqrt`.
    RootArgument,
}

/// The value of a record at one exact argument inside its domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionPointValue {
    /// The slot is empty.
    Empty,
    /// No registered value at the point.
    NoValue,
    /// 0.
    Zero,
    /// 1.
    One,
    /// The argument itself, which the roots return at their fixed points 0
    /// and 1.
    Argument,
    /// 0, written as the multiple $0 \pi$ like the other values of the
    /// inverse trigonometric functions; a multiple $q \pi$ is the product of
    /// the rational $q$ and $\pi$.
    ZeroPi,
    /// $\pi/2$.
    HalfPi,
    /// $-\pi/2$.
    MinusHalfPi,
    /// $\pi$.
    Pi,
    /// $\pi/4$.
    QuarterPi,
    /// $-\pi/4$.
    MinusQuarterPi,
}

/// The values of a record on a family of exact arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionFamily {
    /// The slot is empty.
    Empty,
    /// No family.
    NoFamily,
    /// The rational multiples $q \pi$ with an integer $2q$: the value at the
    /// quarter turn $k = 2q \bmod 4$ is entry $k$ of the quarter-turn table.
    QuarterTurns,
    /// The principal roots of rationals: degree 1 is the identity, and a
    /// rational root has its exact principal value.
    PrincipalRoots,
    /// The modulus of exact constants: $\lvert q \rvert$,
    /// $\lvert c \pi \rvert = \lvert c \rvert \pi$ and
    /// $\lvert c i \rvert = \lvert c \rvert$ for rationals $q$ and $c$.
    Modulus,
}

/// The value of a record at a quarter turn, an argument $k \pi / 2$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionQuarterValue {
    /// The slot is empty.
    Empty,
    /// The record has no quarter-turn family.
    NoQuarterTurns,
    /// 0.
    Zero,
    /// 1.
    One,
    /// $-1$.
    MinusOne,
    /// Outside the domain.
    Undefined,
}

/// The exact arguments outside the domain of a record that the call
/// constructor rejects: domain facts, never values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionUndefinedPoints {
    /// The slot is empty.
    Empty,
    /// No such argument.
    NoPoints,
    /// $q \pi$ with $2q$ an odd integer.
    OddHalfPiMultiples,
    /// A rational $q$ with $\lvert q \rvert \gt 1$, and $c i$ with a
    /// rational $c \ne 0$.
    BeyondOneOrImaginary,
    /// $c i$ with a rational $c \ne 0$.
    ImaginaryMultiples,
    /// 0.
    Zero,
    /// A degree that is 0, a negative integer, a rational that is not an
    /// integer, $\pi$ or $i$.
    ExcludedDegrees,
}

/// The period of a record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionPeriod {
    /// The slot is empty.
    Empty,
    /// No period.
    NoPeriod,
    /// $2 \pi$.
    TwoPi,
    /// $\pi$.
    Pi,
    /// $2 \pi i$.
    TwoPiI,
}

/// The parity of a record, or its reflection formula.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionParity {
    /// The slot is empty.
    Empty,
    /// No parity and no reflection formula.
    NoParity,
    /// $f(-u) = -f(u)$.
    Odd,
    /// $f(-u) = f(u)$.
    Even,
    /// $f(-u) = \pi - f(u)$.
    Reflection,
}

/// The rewrites of a call under a proved sign of its argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionSignRule {
    /// The slot is empty.
    Empty,
    /// No sign rule.
    NoSignRule,
    /// $\lvert u \rvert = u$ for a proved nonnegative $u$, and
    /// $\lvert u \rvert = -u$ for a proved nonpositive $u$.
    Modulus,
}

/// Where a record satisfies $f(\bar u) = \overline{f(u)}$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionConjugation {
    /// The slot is empty.
    Empty,
    /// At every argument of the domain.
    OnDomain,
    /// At every argument of the domain off the cut that the cut slot gives at
    /// the degree of the call. On the cut the value is that from the closed
    /// side, and its conjugate that from the other side.
    OffCut,
}

/// The zeros and the poles of a record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionZerosAndPoles {
    /// The slot is empty.
    Empty,
    /// The zeros $k \pi$ for the integers $k$, and no pole.
    MultiplesOfPi,
    /// The zeros $q \pi$ with $2q$ an odd integer, and no pole.
    OddHalfPiMultiples,
    /// The zeros $k \pi$ for the integers $k$, and the simple poles $q \pi$
    /// with $2q$ an odd integer, outside the domain.
    TangentZerosAndPoles,
    /// The one zero 0, and no pole.
    ZeroAtOrigin,
    /// The one zero 1, and no pole.
    ZeroAtOne,
    /// No zero and no pole.
    NoZeros,
}

/// The derivative formula of a record with respect to its operand $u$: a
/// template in $u$ and in the call itself, which differentiation multiplies
/// by the derivative of $u$ (the chain rule).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionDerivative {
    /// The slot is empty.
    Empty,
    /// $\cos u$.
    Cosine,
    /// $-\sin u$.
    NegativeSine,
    /// $\cos(u)^{-2}$.
    InverseCosineSquared,
    /// $1/\sqrt{1 - u^2}$, with the principal square root.
    Arcsine,
    /// $-1/\sqrt{1 - u^2}$, with the principal square root.
    Arccosine,
    /// $1/(1 + u^2)$.
    Arctangent,
    /// The call itself.
    Itself,
    /// $u^{-1}$.
    Reciprocal,
    /// $(1/n) (\mathrm{rootn}(u, n)^{n - 1})^{-1}$ for the degree $n$ of the
    /// call, and 1 for degree 1.
    RootPower,
    /// The sign of $u$: 1 for $u \gt 0$ and $-1$ for $u \lt 0$, built as the
    /// case split on the two half-lines of its region, which keeps the
    /// derivative formal at 0. It is the only formula with the region
    /// `RealNonzero`, which adds no condition of its own.
    Sign,
}

/// Where the derivative formula of a record holds: the region on the
/// holomorphic path and the region on real paths, along which the variable
/// and the operand are proved real. Elsewhere the derivative stays formal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionRegion {
    /// The slot is empty.
    Empty,
    /// The whole domain on every path: the domain is open and the record is
    /// holomorphic on it.
    Domain,
    /// Off the cut on every path, and along real paths on the whole domain,
    /// which leaves out the branch point.
    OffCutOrRealDomain,
    /// Off the cut on every path, and along real paths at nonzero operands:
    /// the branch point 0 is in the domain, and the record is not
    /// differentiable there.
    OffCutOrRealNonzero,
    /// Along real paths only, on the open interval $(-1, 1)$; the
    /// holomorphic region is empty.
    RealOpenUnitInterval,
    /// Along real paths only, on the whole real line; the holomorphic region
    /// is empty.
    RealLine,
    /// Along real paths only, at nonzero operands; the holomorphic region is
    /// empty. The region adds no condition to the formula.
    RealNonzero,
}

/// How the truncated power series of a call is computed from the series of
/// its operand at a regular point, one whose constant term $u_0$ is in the
/// domain of the call and, for a record with a cut, off the cut.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionExpansion {
    /// The slot is empty.
    Empty,
    /// The recurrence $n f_n = \sum_k k u_k f_{n-k}$ of $f' = u' f$.
    ExponentialRecurrence,
    /// The coupled recurrences of $s' = u' c$ and $c' = -u' s$, giving $s$.
    SineRecurrence,
    /// The coupled recurrences of $s' = u' c$ and $c' = -u' s$, giving $c$.
    CosineRecurrence,
    /// The value at $u_0$ plus the integral of $u'/u$.
    LogarithmIntegral,
    /// The quotient of the sine and the cosine series.
    TangentQuotient,
    /// $\exp(\log(u)/n)$ for the degree $n$ of the call.
    RootComposition,
    /// The series of $u$ for a constant term proved positive, and of $-u$
    /// for one proved negative.
    ModulusSign,
}

/// The Laurent expansion of a call at a pole of its record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionPoleExpansion {
    /// The slot is empty.
    Empty,
    /// The record has no pole.
    NoPoles,
    /// The quotient of the sine and the cosine series, at a constant term
    /// where the cosine vanishes.
    TangentQuotient,
}

/// The expansion of a call at a branch point of its record. The slot is in
/// the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionBranchExpansion {
    /// The slot is empty.
    Empty,
}

/// The behaviour of a call as its operand tends to $+\infty$ or to
/// $-\infty$. The two slots are in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionAtInfinity {
    /// The slot is empty.
    Empty,
}

/// The enclosure kernel of a record. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionKernel {
    /// The slot is empty.
    Empty,
}

/// The condition that the enclosure of the operand must meet before the
/// kernel runs. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionRequirement {
    /// The slot is empty.
    Empty,
}

/// Whether a call of the record may occur in Taylor-model integration. The
/// slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionTaylorModel {
    /// The slot is empty.
    Empty,
}

/// The binary64 scalar entry of a record. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionBinary64 {
    /// The slot is empty.
    Empty,
}

/// The antiderivatives of a record with respect to its operand. The slot is
/// in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionAntiderivative {
    /// The slot is empty.
    Empty,
}

/// The integrands whose primitive is a call of the record. The slot is in
/// the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionIntegrationResult {
    /// The slot is empty.
    Empty,
}

/// Whether the derivatives of a record stay within a finite family up to
/// constant factors. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionDerivativeFamily {
    /// The slot is empty.
    Empty,
}

/// The sums whose closed form is a call of the record. The slot is in the
/// exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionSummation {
    /// The slot is empty.
    Empty,
}

/// The solutions of $f(u) = t$. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionInversion {
    /// The slot is empty.
    Empty,
}

/// The limits of expressions with the record that neither its continuity
/// nor its expansions give. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionLimitRule {
    /// The slot is empty.
    Empty,
}

/// The names of the record in structured output. The slot is in the
/// exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionOutputName {
    /// The slot is empty.
    Empty,
}

/// The dimensions of the arguments and results of a record, and which of
/// them are angles. The slot is in the exemption list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionDimensions {
    /// The slot is empty.
    Empty,
}

/// Where a record is analytic, and whether it is real on the real axis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionAnalyticity {
    /// The slot is empty.
    Empty,
    /// Holomorphic on the whole complex plane, and real on the real axis.
    Entire,
    /// Holomorphic on its domain, with poles outside it, and real on the
    /// reals of its domain.
    Meromorphic,
    /// Real-analytic on the open interval $(-1, 1)$, and not at the ends of
    /// its domain; it has no complex domain.
    RealAnalyticOnOpenUnitInterval,
    /// Real-analytic on the whole real line; it has no complex domain.
    RealAnalyticOnReals,
    /// Holomorphic on its domain off the cut that the cut slot gives at the
    /// degree of the call, and real on the positive reals.
    OffCut,
    /// Not analytic: holomorphic on no open set, and not real-analytic at 0.
    NotAnalytic,
}

/// The classes of the values of a call, from the classes of its argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionInference {
    /// The slot is empty.
    Empty,
    /// Real on the whole domain.
    RealValued,
    /// Real for a real argument.
    RealOnReals,
    /// The modulus: 0 for a zero argument, positive for a nonzero argument
    /// and nonnegative for every argument.
    Modulus,
    /// Positive for a real argument and nonzero for every argument.
    Exponential,
    /// Real for a positive argument.
    Logarithm,
    /// The principal root: imaginary for a negative argument, positive for a
    /// positive argument, nonnegative for a nonnegative argument and nonzero
    /// for a nonzero argument.
    Root,
}

/// The 39 slots of a record, one field each, in the order of the contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FunctionItems {
    /// Node, domain and branch cuts: the domain label.
    pub(crate) domain: FunctionDomain,
    /// Node, domain and branch cuts: complex or real-only support.
    pub(crate) support: FunctionSupport,
    /// Node, domain and branch cuts: the cut and its sharp part.
    pub(crate) cut: FunctionCut,
    /// Node, domain and branch cuts: the closed side of the cut.
    pub(crate) closed_side: FunctionClosedSide,
    /// Node, domain and branch cuts: the value on the cut.
    pub(crate) cut_value: FunctionCutValue,
    /// Node, domain and branch cuts: the principal range.
    pub(crate) principal_range: FunctionRange,
    /// Special values and symmetries: the value at 0.
    pub(crate) at_zero: FunctionPointValue,
    /// Special values and symmetries: the value at 1.
    pub(crate) at_one: FunctionPointValue,
    /// Special values and symmetries: the value at $-1$.
    pub(crate) at_minus_one: FunctionPointValue,
    /// Special values and symmetries: the value at $i$.
    pub(crate) at_unit: FunctionPointValue,
    /// Special values and symmetries: the value family.
    pub(crate) family: FunctionFamily,
    /// Special values and symmetries: the values at the quarter turns 0, 1,
    /// 2 and 3 of the `QuarterTurns` family, and `NoQuarterTurns` for every
    /// other family.
    pub(crate) quarter_turns: [FunctionQuarterValue; 4],
    /// Special values and symmetries: the undefined points.
    pub(crate) undefined_points: FunctionUndefinedPoints,
    /// Special values and symmetries: the period.
    pub(crate) period: FunctionPeriod,
    /// Special values and symmetries: the parity.
    pub(crate) parity: FunctionParity,
    /// Special values and symmetries: the sign rules.
    pub(crate) sign_rule: FunctionSignRule,
    /// Special values and symmetries: the conjugate symmetry.
    pub(crate) conjugation: FunctionConjugation,
    /// Special values and symmetries: the zeros and the poles.
    pub(crate) zeros_and_poles: FunctionZerosAndPoles,
    /// Derivatives: the formula.
    pub(crate) derivative: FunctionDerivative,
    /// Derivatives: the regions where the formula holds.
    pub(crate) region: FunctionRegion,
    /// Series: the regular-point method, with its validity condition.
    pub(crate) expansion: FunctionExpansion,
    /// Series: the expansion at a pole.
    pub(crate) pole_expansion: FunctionPoleExpansion,
    /// Series: the expansion at a branch point.
    pub(crate) branch_expansion: FunctionBranchExpansion,
    /// Series: the behaviour as the operand tends to $+\infty$.
    pub(crate) at_plus_infinity: FunctionAtInfinity,
    /// Series: the behaviour as the operand tends to $-\infty$.
    pub(crate) at_minus_infinity: FunctionAtInfinity,
    /// Numerical evaluation: the enclosure kernel.
    pub(crate) kernel: FunctionKernel,
    /// Numerical evaluation: the argument requirement.
    pub(crate) requirement: FunctionRequirement,
    /// Numerical evaluation: the Taylor-model eligibility.
    pub(crate) taylor_model: FunctionTaylorModel,
    /// Numerical evaluation: the binary64 entry.
    pub(crate) binary64: FunctionBinary64,
    /// Connection rules: the antiderivatives.
    pub(crate) antiderivative: FunctionAntiderivative,
    /// Connection rules: the integration results.
    pub(crate) integration_result: FunctionIntegrationResult,
    /// Connection rules: the derivative-closed family.
    pub(crate) derivative_family: FunctionDerivativeFamily,
    /// Connection rules: the summation.
    pub(crate) summation: FunctionSummation,
    /// Connection rules: the equation inversion.
    pub(crate) inversion: FunctionInversion,
    /// Connection rules: the limit rules.
    pub(crate) limit_rule: FunctionLimitRule,
    /// Other fields: the output names.
    pub(crate) output_name: FunctionOutputName,
    /// Other fields: the dimensions and angles.
    pub(crate) dimensions: FunctionDimensions,
    /// Other fields: the analyticity.
    pub(crate) analyticity: FunctionAnalyticity,
    /// Other fields: the property inference.
    pub(crate) inference: FunctionInference,
}

/// The items of the records, in the order of `RECORDS`.
static ITEMS: [FunctionItems; 11] = [
    // sin
    FunctionItems {
        domain: FunctionDomain::Total,
        support: FunctionSupport::Complex,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::SingleValued,
        at_zero: FunctionPointValue::Zero,
        at_one: FunctionPointValue::NoValue,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::QuarterTurns,
        quarter_turns: [
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::One,
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::MinusOne,
        ],
        undefined_points: FunctionUndefinedPoints::NoPoints,
        period: FunctionPeriod::TwoPi,
        parity: FunctionParity::Odd,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::MultiplesOfPi,
        derivative: FunctionDerivative::Cosine,
        region: FunctionRegion::Domain,
        expansion: FunctionExpansion::SineRecurrence,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::Entire,
        inference: FunctionInference::RealOnReals,
    },
    // cos
    FunctionItems {
        domain: FunctionDomain::Total,
        support: FunctionSupport::Complex,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::SingleValued,
        at_zero: FunctionPointValue::One,
        at_one: FunctionPointValue::NoValue,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::QuarterTurns,
        quarter_turns: [
            FunctionQuarterValue::One,
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::MinusOne,
            FunctionQuarterValue::Zero,
        ],
        undefined_points: FunctionUndefinedPoints::NoPoints,
        period: FunctionPeriod::TwoPi,
        parity: FunctionParity::Even,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::OddHalfPiMultiples,
        derivative: FunctionDerivative::NegativeSine,
        region: FunctionRegion::Domain,
        expansion: FunctionExpansion::CosineRecurrence,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::Entire,
        inference: FunctionInference::RealOnReals,
    },
    // tan
    FunctionItems {
        domain: FunctionDomain::CosineNonzero,
        support: FunctionSupport::Complex,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::SingleValued,
        at_zero: FunctionPointValue::Zero,
        at_one: FunctionPointValue::NoValue,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::QuarterTurns,
        quarter_turns: [
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::Undefined,
            FunctionQuarterValue::Zero,
            FunctionQuarterValue::Undefined,
        ],
        undefined_points: FunctionUndefinedPoints::OddHalfPiMultiples,
        period: FunctionPeriod::Pi,
        parity: FunctionParity::Odd,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::TangentZerosAndPoles,
        derivative: FunctionDerivative::InverseCosineSquared,
        region: FunctionRegion::Domain,
        expansion: FunctionExpansion::TangentQuotient,
        pole_expansion: FunctionPoleExpansion::TangentQuotient,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::Meromorphic,
        inference: FunctionInference::RealOnReals,
    },
    // asin
    FunctionItems {
        domain: FunctionDomain::RealUnitInterval,
        support: FunctionSupport::Real,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::ClosedHalfPi,
        at_zero: FunctionPointValue::ZeroPi,
        at_one: FunctionPointValue::HalfPi,
        at_minus_one: FunctionPointValue::MinusHalfPi,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::NoFamily,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::BeyondOneOrImaginary,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::Odd,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOrigin,
        derivative: FunctionDerivative::Arcsine,
        region: FunctionRegion::RealOpenUnitInterval,
        expansion: FunctionExpansion::Empty,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::RealAnalyticOnOpenUnitInterval,
        inference: FunctionInference::RealValued,
    },
    // acos
    FunctionItems {
        domain: FunctionDomain::RealUnitInterval,
        support: FunctionSupport::Real,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::ZeroToPi,
        at_zero: FunctionPointValue::HalfPi,
        at_one: FunctionPointValue::ZeroPi,
        at_minus_one: FunctionPointValue::Pi,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::NoFamily,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::BeyondOneOrImaginary,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::Reflection,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOne,
        derivative: FunctionDerivative::Arccosine,
        region: FunctionRegion::RealOpenUnitInterval,
        expansion: FunctionExpansion::Empty,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::RealAnalyticOnOpenUnitInterval,
        inference: FunctionInference::RealValued,
    },
    // atan
    FunctionItems {
        domain: FunctionDomain::Real,
        support: FunctionSupport::Real,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::OpenHalfPi,
        at_zero: FunctionPointValue::ZeroPi,
        at_one: FunctionPointValue::QuarterPi,
        at_minus_one: FunctionPointValue::MinusQuarterPi,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::NoFamily,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::ImaginaryMultiples,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::Odd,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOrigin,
        derivative: FunctionDerivative::Arctangent,
        region: FunctionRegion::RealLine,
        expansion: FunctionExpansion::Empty,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::RealAnalyticOnReals,
        inference: FunctionInference::RealValued,
    },
    // exp
    FunctionItems {
        domain: FunctionDomain::Total,
        support: FunctionSupport::Complex,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::SingleValued,
        at_zero: FunctionPointValue::One,
        at_one: FunctionPointValue::NoValue,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::NoFamily,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::NoPoints,
        period: FunctionPeriod::TwoPiI,
        parity: FunctionParity::NoParity,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::NoZeros,
        derivative: FunctionDerivative::Itself,
        region: FunctionRegion::Domain,
        expansion: FunctionExpansion::ExponentialRecurrence,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::Entire,
        inference: FunctionInference::Exponential,
    },
    // log
    FunctionItems {
        domain: FunctionDomain::Nonzero,
        support: FunctionSupport::Complex,
        cut: FunctionCut::Logarithm,
        closed_side: FunctionClosedSide::Above,
        cut_value: FunctionCutValue::Logarithm,
        principal_range: FunctionRange::LogarithmStrip,
        at_zero: FunctionPointValue::NoValue,
        at_one: FunctionPointValue::Zero,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::NoFamily,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::Zero,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::NoParity,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OffCut,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOne,
        derivative: FunctionDerivative::Reciprocal,
        region: FunctionRegion::OffCutOrRealDomain,
        expansion: FunctionExpansion::LogarithmIntegral,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::OffCut,
        inference: FunctionInference::Logarithm,
    },
    // sqrt
    FunctionItems {
        domain: FunctionDomain::Total,
        support: FunctionSupport::Complex,
        cut: FunctionCut::Root,
        closed_side: FunctionClosedSide::Above,
        cut_value: FunctionCutValue::Root,
        principal_range: FunctionRange::RootArgument,
        at_zero: FunctionPointValue::Argument,
        at_one: FunctionPointValue::Argument,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::PrincipalRoots,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::NoPoints,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::NoParity,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OffCut,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOrigin,
        derivative: FunctionDerivative::RootPower,
        region: FunctionRegion::OffCutOrRealNonzero,
        expansion: FunctionExpansion::RootComposition,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::OffCut,
        inference: FunctionInference::Root,
    },
    // rootn
    FunctionItems {
        domain: FunctionDomain::PositiveDegree,
        support: FunctionSupport::Complex,
        cut: FunctionCut::RootFromDegreeTwo,
        closed_side: FunctionClosedSide::Above,
        cut_value: FunctionCutValue::Root,
        principal_range: FunctionRange::RootArgument,
        at_zero: FunctionPointValue::Argument,
        at_one: FunctionPointValue::Argument,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::NoValue,
        family: FunctionFamily::PrincipalRoots,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::ExcludedDegrees,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::NoParity,
        sign_rule: FunctionSignRule::NoSignRule,
        conjugation: FunctionConjugation::OffCut,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOrigin,
        derivative: FunctionDerivative::RootPower,
        region: FunctionRegion::OffCutOrRealNonzero,
        expansion: FunctionExpansion::RootComposition,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::OffCut,
        inference: FunctionInference::Root,
    },
    // abs
    FunctionItems {
        domain: FunctionDomain::Total,
        support: FunctionSupport::Complex,
        cut: FunctionCut::NoCut,
        closed_side: FunctionClosedSide::NoCut,
        cut_value: FunctionCutValue::NoCut,
        principal_range: FunctionRange::SingleValued,
        at_zero: FunctionPointValue::NoValue,
        at_one: FunctionPointValue::NoValue,
        at_minus_one: FunctionPointValue::NoValue,
        at_unit: FunctionPointValue::One,
        family: FunctionFamily::Modulus,
        quarter_turns: [
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
            FunctionQuarterValue::NoQuarterTurns,
        ],
        undefined_points: FunctionUndefinedPoints::NoPoints,
        period: FunctionPeriod::NoPeriod,
        parity: FunctionParity::Even,
        sign_rule: FunctionSignRule::Modulus,
        conjugation: FunctionConjugation::OnDomain,
        zeros_and_poles: FunctionZerosAndPoles::ZeroAtOrigin,
        derivative: FunctionDerivative::Sign,
        region: FunctionRegion::RealNonzero,
        expansion: FunctionExpansion::ModulusSign,
        pole_expansion: FunctionPoleExpansion::NoPoles,
        branch_expansion: FunctionBranchExpansion::Empty,
        at_plus_infinity: FunctionAtInfinity::Empty,
        at_minus_infinity: FunctionAtInfinity::Empty,
        kernel: FunctionKernel::Empty,
        requirement: FunctionRequirement::Empty,
        taylor_model: FunctionTaylorModel::Empty,
        binary64: FunctionBinary64::Empty,
        antiderivative: FunctionAntiderivative::Empty,
        integration_result: FunctionIntegrationResult::Empty,
        derivative_family: FunctionDerivativeFamily::Empty,
        summation: FunctionSummation::Empty,
        inversion: FunctionInversion::Empty,
        limit_rule: FunctionLimitRule::Empty,
        output_name: FunctionOutputName::Empty,
        dimensions: FunctionDimensions::Empty,
        analyticity: FunctionAnalyticity::NotAnalytic,
        inference: FunctionInference::Modulus,
    },
];

/// A copy of the items of the record of `id`.
pub(crate) fn items(id: FunctionId) -> FunctionItems {
    match id {
        FunctionId::Sin => ITEMS[0],
        FunctionId::Cos => ITEMS[1],
        FunctionId::Tan => ITEMS[2],
        FunctionId::Asin => ITEMS[3],
        FunctionId::Acos => ITEMS[4],
        FunctionId::Atan => ITEMS[5],
        FunctionId::Exp => ITEMS[6],
        FunctionId::Log => ITEMS[7],
        FunctionId::Sqrt => ITEMS[8],
        FunctionId::Rootn => ITEMS[9],
        FunctionId::Abs => ITEMS[10],
    }
}

/// The identifier of an entry of the identity list, named like the entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionIdentityId {
    /// $\mathrm{rootn}(u, 2) = \sqrt{u}$, for the literal degree 2.
    SqrtEqRootn,
    /// $\mathrm{rootn}(u, 1) = u$, for the literal degree 1.
    RootnOne,
    /// $\lvert \lvert u \rvert \rvert = \lvert u \rvert$.
    AbsAbs,
    /// $\mathrm{rootn}(u, n)^k = u^{\lfloor k/n \rfloor} \mathrm{rootn}(u, n)^{k \bmod n}$
    /// for a literal degree $n$ and every integer $k \ge 1$, with `sqrt` as
    /// the root of degree 2.
    RootPow,
    /// $\sqrt{u^2} = \lvert u \rvert$.
    SqrtSq,
    /// $\log(\exp u) = u$.
    LogExp,
    /// $\exp(\log u) = u$.
    ExpLog,
    /// $\sin(\arcsin u) = u$.
    SinAsin,
    /// $\cos(\arccos u) = u$.
    CosAcos,
    /// $\tan(\arctan u) = u$.
    TanAtan,
}

/// The applicability class of an entry of the identity list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionIdentityClass {
    /// Both sides have the same domain, and the entry needs no assumption.
    Unconditional,
    /// The entry holds where its condition holds, an assumption about the
    /// operand.
    UnderAssumption,
    /// The left side is defined exactly where its condition holds, and the
    /// right side everywhere: the entry keeps the domain of the left side
    /// as a condition.
    KeepsLeftDomain,
}

/// The condition of an entry of the identity list, on its operand $u$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionIdentityCondition {
    /// No condition.
    NoCondition,
    /// A real $u$.
    Real,
    /// $-\pi \lt \mathrm{Im}\, u \le \pi$.
    PrincipalStrip,
    /// $u \ne 0$.
    Nonzero,
    /// A real $u$ with $-1 \le u \le 1$.
    RealUnitInterval,
}

/// An entry of the identity list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FunctionIdentity {
    pub(crate) id: FunctionIdentityId,
    pub(crate) class: FunctionIdentityClass,
    /// The assumption of an entry under assumptions, the domain of the left
    /// side of an entry that keeps it, and `NoCondition` otherwise.
    pub(crate) condition: FunctionIdentityCondition,
    /// The records that the entry names, in the first `count` positions; the
    /// positions from `count` on repeat the first record.
    pub(crate) records: [FunctionId; 2],
    pub(crate) count: usize,
}

/// The entries of the identity list, in the order of their identifiers.
static IDENTITIES: [FunctionIdentity; 10] = [
    FunctionIdentity {
        id: FunctionIdentityId::SqrtEqRootn,
        class: FunctionIdentityClass::Unconditional,
        condition: FunctionIdentityCondition::NoCondition,
        records: [FunctionId::Sqrt, FunctionId::Rootn],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::RootnOne,
        class: FunctionIdentityClass::Unconditional,
        condition: FunctionIdentityCondition::NoCondition,
        records: [FunctionId::Rootn, FunctionId::Rootn],
        count: 1,
    },
    FunctionIdentity {
        id: FunctionIdentityId::AbsAbs,
        class: FunctionIdentityClass::Unconditional,
        condition: FunctionIdentityCondition::NoCondition,
        records: [FunctionId::Abs, FunctionId::Abs],
        count: 1,
    },
    FunctionIdentity {
        id: FunctionIdentityId::RootPow,
        class: FunctionIdentityClass::Unconditional,
        condition: FunctionIdentityCondition::NoCondition,
        records: [FunctionId::Sqrt, FunctionId::Rootn],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::SqrtSq,
        class: FunctionIdentityClass::UnderAssumption,
        condition: FunctionIdentityCondition::Real,
        records: [FunctionId::Sqrt, FunctionId::Abs],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::LogExp,
        class: FunctionIdentityClass::UnderAssumption,
        condition: FunctionIdentityCondition::PrincipalStrip,
        records: [FunctionId::Log, FunctionId::Exp],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::ExpLog,
        class: FunctionIdentityClass::KeepsLeftDomain,
        condition: FunctionIdentityCondition::Nonzero,
        records: [FunctionId::Exp, FunctionId::Log],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::SinAsin,
        class: FunctionIdentityClass::KeepsLeftDomain,
        condition: FunctionIdentityCondition::RealUnitInterval,
        records: [FunctionId::Sin, FunctionId::Asin],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::CosAcos,
        class: FunctionIdentityClass::KeepsLeftDomain,
        condition: FunctionIdentityCondition::RealUnitInterval,
        records: [FunctionId::Cos, FunctionId::Acos],
        count: 2,
    },
    FunctionIdentity {
        id: FunctionIdentityId::TanAtan,
        class: FunctionIdentityClass::KeepsLeftDomain,
        condition: FunctionIdentityCondition::Real,
        records: [FunctionId::Tan, FunctionId::Atan],
        count: 2,
    },
];

/// A copy of the entry `id` of the identity list.
pub(crate) fn identity(id: FunctionIdentityId) -> FunctionIdentity {
    match id {
        FunctionIdentityId::SqrtEqRootn => IDENTITIES[0],
        FunctionIdentityId::RootnOne => IDENTITIES[1],
        FunctionIdentityId::AbsAbs => IDENTITIES[2],
        FunctionIdentityId::RootPow => IDENTITIES[3],
        FunctionIdentityId::SqrtSq => IDENTITIES[4],
        FunctionIdentityId::LogExp => IDENTITIES[5],
        FunctionIdentityId::ExpLog => IDENTITIES[6],
        FunctionIdentityId::SinAsin => IDENTITIES[7],
        FunctionIdentityId::CosAcos => IDENTITIES[8],
        FunctionIdentityId::TanAtan => IDENTITIES[9],
    }
}

#[cfg(test)]
mod tests;
