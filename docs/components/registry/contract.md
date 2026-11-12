# Function registry

This contract states the function registry of kalyx: the static record of
each of the eleven functions of function expressions, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `exp`, `log`, `sqrt`, `rootn` and `abs`, with the
identity fields and the 39 slots of its schema; the identity list, which
relates calls of several records or nested calls; the exemption list; and
the lookup of a name. It applies to the module `src/registry.rs`, with its
tests in `src/registry/tests.rs`. The
[architecture](../../architecture.md#function-knowledge) places the
component among the foundations and states that function knowledge lives
only in the registry. The errors belong to the
[errors and result states](../errors/contract.md).

**Status.** Implemented in `src/registry.rs`, at tier A1 (tested with a
written contract); an upgrade to tier A3 is planned for release 0.3. The
registry is a crate-internal module: it has no public interface, and the
public names of the crate root do not change. It is ported from the
registry of the earlier implementation, as [PORTING](../../../PORTING.md)
records. No code outside the module reads it yet. Its first production
caller is planned to be the function-expression baseline of release 0.2,
with the derivatives and Taylor series of function expressions; the call
constructor of the term core is planned to read its records in the same
release. The registry fixes all its slots at once, the one exception that
the [architecture](../../architecture.md#components) lists.

## Scope

- **Included.** The identity fields of the eleven records; the record
  schema of 39 slots and the value of every slot for every record; the
  meaning of each domain label as a condition; the identity list of ten
  entries; the exemption list of 15 slots; lookup by name and the entry
  that reports a name that the registry does not hold; the representation
  of the records for proof.
- **Planned.** The checks of a call, the number of arguments before the
  domain and the degree of `rootn` by the class of its value, in the call
  constructor of the term core; the readers of the slots and of the
  identity list: the call constructor, the scoped rewriting `f-refine`,
  differentiation, the Taylor and Laurent series of function expressions
  and the assumption system; the regular-point method of `asin`, `acos` and
  `atan`, which the Taylor series of function expressions are to fill in
  release 0.2; the completeness and consistency tests of the records; and
  the slots of the [exemption list](#exemption-list), each with its
  release.
- **Excluded.** Declared functions: names resolve only against the
  registry. Aliases: every record has one name.

## Interface

The module is declared as `mod registry;` in `src/lib.rs`, and its items are
`pub(crate)`:

- `FunctionId`, the identifier of a record, with the eleven variants `Sin`,
  `Cos`, `Tan`, `Asin`, `Acos`, `Atan`, `Exp`, `Log`, `Sqrt`, `Rootn` and
  `Abs` in the order of the records.
- `FunctionRecord`, the identity fields, with `id`, `name`, `length`,
  `arity` and `roles`, and `FunctionRole`, the role of an argument position,
  `Operand` or `Degree`.
- `lookup(name: &[u8]) -> Option<FunctionId>` and
  `resolve(name: &[u8], span: Option<Span>) -> Result<FunctionId>`, as
  [lookup and the entry](#lookup-and-the-entry) state.
- `record(id: FunctionId) -> FunctionRecord` and
  `items(id: FunctionId) -> FunctionItems`, which return copies of the two
  parts of a record.
- `FunctionItems`, the 39 slots, one field each, and the 35 enumerations of
  the slots, as the [record schema](#the-record-schema) states: the four
  values at points share one enumeration, and so do the two behaviours at
  infinity.
- `FunctionIdentity`, an entry of the [identity list](#identity-list), with
  `FunctionIdentityId`, `FunctionIdentityClass` and
  `FunctionIdentityCondition`, and
  `identity(id: FunctionIdentityId) -> FunctionIdentity`.

No function of the module takes a request context, and none charges work.

## Rules

### Principles

- **Static.** The registry is an immutable table of records fixed at compile
  time. There is no registration at run time and no global mutable state, so
  the meaning of a name never depends on what was registered before it.
- **One identifier per name.** Each registered name has its own record and
  its own identifier, a variant of a fieldless enumeration. The records are
  kept in the order `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `exp`,
  `log`, `sqrt`, `rootn`, `abs`. `sqrt` and `rootn` are separate records,
  and `sqrt(u)` denotes the same value as `rootn(u, 2)`, the entry
  `sqrt_eq_rootn` of the identity list.
- **Function knowledge in the registry only.** What the library knows about
  one registered function is a slot of its record; what relates calls of
  several records, or nested calls, is an entry of the identity list. No
  other module holds such knowledge of its own, as the
  [architecture](../../architecture.md#function-knowledge) states.
- **Names that the registry does not hold.** Lookup finds exactly the record
  of a registered name and nothing for every other name. No registered name
  is one of the words that the architecture reserves by position
  ([reserved names](../../architecture.md#reserved-names)): the constants
  `pi` and `i`, `undefined`, the special forms `piecewise`, `derivative` and
  `substitute`, the literal heads `root` and `croot`, the truth values, the
  condition heads `and`, `or`, `not` and `defined`, the heads of other start
  symbols and the names that are never constants; and no registered name
  starts with `is_`, the prefix of the property predicates.
- **No declared functions.** kalyx does not support declared functions.
  There is no table of declarations to look in, and the entry reports every
  name that the registry does not hold as `Fault(Syntax)`.
- **Lookup and access are free.** Lookup compares the name with the eleven
  registered names, so its work is bounded independently of the input, and
  access from an identifier returns a copy. Neither takes a request context
  or charges work: the registry has no charge point.

### Representation

The registry is written to be proved, in the shapes that the qualification
cases `registry-records` and `registry-items` of the proof tooling
translate:

- A record is plain data, kept in two static tables in the order of the
  records: `RECORDS` holds the identity fields and `ITEMS` the slots, and the
  identity list is a third static table, `IDENTITIES`. The records and the
  entries are `Copy` structures whose fields are fieldless enumerations,
  arrays of them, byte arrays or `usize` counts. Records hold no term,
  closure, function pointer, string or request context, so the module
  depends on no term, `Context` or formatting.
- A name is a byte array of 8 bytes with a length, the name in the first
  `length` bytes followed by zero bytes, written as a zero-padded byte-string
  literal such as `*b"rootn\0\0\0"`; no name is a `&str`.
- Lookup is an index loop over the records that calls the helper `named`,
  which compares the length and then the bytes in a loop of its own. Access
  from an identifier is an exhaustive `match` that returns a copy of the
  record, of its items or of an entry.
- The tables are written out in the source; no macro generates them.
- A slot whose value depends on the degree of `rootn`, such as its cut, is a
  template that its reader instantiates at the degree of the call.
- The only string literal of the module is the message of the error of the
  entry.

### Identity fields

| Field | Content | Code |
| --- | --- | --- |
| Identifier | A variant of the fieldless enumeration `FunctionId`, named like the record | `id` |
| Name | An ASCII letter, followed by ASCII letters, digits and `_`, so that the lexer reads it as one name; at most 8 bytes; unique, and none of the reserved words of [principles](#principles) | `name`, zero-padded, and `length` |
| Aliases | None: every record has one name | — |
| Arity | The fixed number of arguments: 2 for `rootn`, 1 for every other record | `arity` |
| Argument roles | `Operand`, a complex argument, at the first position of every record; `Degree`, the degree $n$ of `rootn`, at its second position: an ordinary value argument, like the operand, and the call is defined only where its value is a positive integer, as the domain label `PositiveDegree` states. The positions from the arity on are unused and hold `Operand` | `roles` |

The checks of a call that read the arity and the roles, a wrong number of
arguments as `Syntax` before any domain and the degree by the class of its
value, are planned for the call constructor of the term core
([rules of the call constructor](../../architecture.md#rules-of-the-call-constructor)).

### The record schema

The schema has 39 slots in seven groups. Each slot is one field of
`FunctionItems`, of a fieldless enumeration, or for the quarter-turn table an
array of four of them; the four values at points share one enumeration,
`FunctionPointValue`, and the two behaviours at infinity share
`FunctionAtInfinity`, and every other slot has its own. Every slot
enumeration has the variant `Empty`, which the
[exemption list](#exemption-list) uses: the 15 slots of the list hold
`Empty` for every record. The regular-point method of `asin`, `acos` and
`atan` holds `Empty` too; it is not in the list, and the Taylor series of
function expressions are planned to fill it in release 0.2. No other slot
of any record holds `Empty`. A value that states that nothing applies, such
as `NoValue`, `NoCut`, `SingleValued` or `NoPoles`, or a region whose
holomorphic part is empty, is an ordinary value of its slot.

| # | Group | Slot | Field | Records filled |
| --- | --- | --- | --- | --- |
| 1 | Node, domain and branch cuts | Domain label | `domain` | 11 |
| 2 | Node, domain and branch cuts | Support | `support` | 11 |
| 3 | Node, domain and branch cuts | Cut and its sharp part | `cut` | 11 |
| 4 | Node, domain and branch cuts | Closed side of the cut | `closed_side` | 11 |
| 5 | Node, domain and branch cuts | Value on the cut | `cut_value` | 11 |
| 6 | Node, domain and branch cuts | Principal range | `principal_range` | 11 |
| 7 | Special values and symmetries | Value at 0 | `at_zero` | 11 |
| 8 | Special values and symmetries | Value at 1 | `at_one` | 11 |
| 9 | Special values and symmetries | Value at $-1$ | `at_minus_one` | 11 |
| 10 | Special values and symmetries | Value at $i$ | `at_unit` | 11 |
| 11 | Special values and symmetries | Value family | `family` | 11 |
| 12 | Special values and symmetries | Quarter-turn table | `quarter_turns` | 11 |
| 13 | Special values and symmetries | Undefined points | `undefined_points` | 11 |
| 14 | Special values and symmetries | Period | `period` | 11 |
| 15 | Special values and symmetries | Parity | `parity` | 11 |
| 16 | Special values and symmetries | Sign rules | `sign_rule` | 11 |
| 17 | Special values and symmetries | Conjugate symmetry | `conjugation` | 11 |
| 18 | Special values and symmetries | Zeros and poles | `zeros_and_poles` | 11 |
| 19 | Derivatives | Derivative formula | `derivative` | 11 |
| 20 | Derivatives | Regions | `region` | 11 |
| 21 | Series | Regular-point method, with its validity condition | `expansion` | 8 |
| 22 | Series | Expansion at a pole | `pole_expansion` | 11 |
| 23 | Series | Expansion at a branch point | `branch_expansion` | exempt |
| 24 | Series | Behaviour as the operand tends to $+\infty$ | `at_plus_infinity` | exempt |
| 25 | Series | Behaviour as the operand tends to $-\infty$ | `at_minus_infinity` | exempt |
| 26 | Numerical evaluation | Enclosure kernel | `kernel` | exempt |
| 27 | Numerical evaluation | Argument requirement | `requirement` | exempt |
| 28 | Numerical evaluation | Taylor-model eligibility | `taylor_model` | exempt |
| 29 | Numerical evaluation | binary64 entry | `binary64` | exempt |
| 30 | Connection rules | Antiderivatives | `antiderivative` | exempt |
| 31 | Connection rules | Integration results | `integration_result` | exempt |
| 32 | Connection rules | Derivative-closed family | `derivative_family` | exempt |
| 33 | Connection rules | Summation | `summation` | exempt |
| 34 | Connection rules | Equation inversion | `inversion` | exempt |
| 35 | Connection rules | Limit rules | `limit_rule` | exempt |
| 36 | Other fields | Output names | `output_name` | exempt |
| 37 | Other fields | Dimensions and angles | `dimensions` | exempt |
| 38 | Other fields | Analyticity | `analyticity` | 11 |
| 39 | Other fields | Property inference | `inference` | 11 |

So 24 slots are filled, 23 for the eleven records and the regular-point
method for eight of them, and 15 are exempt. The sources that a record
relies on are not a slot: they are the DLMF sections of the
[normative source](#normative-source).

### Node, domain and branch cuts

| Record | Domain label | Support | Cut | Closed side | Value on the cut | Principal range |
| --- | --- | --- | --- | --- | --- | --- |
| `sin` | `Total` | `Complex` | `NoCut` | `NoCut` | `NoCut` | `SingleValued` |
| `cos` | `Total` | `Complex` | `NoCut` | `NoCut` | `NoCut` | `SingleValued` |
| `tan` | `CosineNonzero` | `Complex` | `NoCut` | `NoCut` | `NoCut` | `SingleValued` |
| `asin` | `RealUnitInterval` | `Real` | `NoCut` | `NoCut` | `NoCut` | `ClosedHalfPi` |
| `acos` | `RealUnitInterval` | `Real` | `NoCut` | `NoCut` | `NoCut` | `ZeroToPi` |
| `atan` | `Real` | `Real` | `NoCut` | `NoCut` | `NoCut` | `OpenHalfPi` |
| `exp` | `Total` | `Complex` | `NoCut` | `NoCut` | `NoCut` | `SingleValued` |
| `log` | `Nonzero` | `Complex` | `Logarithm` | `Above` | `Logarithm` | `LogarithmStrip` |
| `sqrt` | `Total` | `Complex` | `Root` | `Above` | `Root` | `RootArgument` |
| `rootn` | `PositiveDegree` | `Complex` | `RootFromDegreeTwo` | `Above` | `Root` | `RootArgument` |
| `abs` | `Total` | `Complex` | `NoCut` | `NoCut` | `NoCut` | `SingleValued` |

The domain labels are fieldless; each stands for a condition on the operand
$u$ and the degree $n$ under which the record has a value, exactly: the
record is defined if and only if the condition holds. The conditions are
written in the notation of the [conditions](../../architecture.md#conditions)
of function values, which are planned for release 0.2, with comparisons and
the predicates `is_real` and `is_integer` of the properties real and integer
of the planned assumption system:

| Label | Condition | Records |
| --- | --- | --- |
| `Total` | `true` | `sin`, `cos`, `exp`, `sqrt`, `abs` |
| `CosineNonzero` | `cos(u) != 0` | `tan` |
| `RealUnitInterval` | `and(is_real(u), u >= -1, u <= 1)` | `asin`, `acos` |
| `Real` | `is_real(u)` | `atan` |
| `Nonzero` | `u != 0` | `log` |
| `PositiveDegree` | `and(is_integer(n), n >= 1)` | `rootn` |

When the builder of function values builds a call of `tan`, `asin`, `acos`,
`atan`, `log` or `rootn`, it is planned to add the condition of its label to
the condition of the value
([domains of calls](../../architecture.md#domains-of-calls)).

The other slots of the group:

- **Support.** `Complex`: complex arguments. `Real`: real arguments only,
  with real values, so the record is continuous only along real paths.
- **Cut and its sharp part.** The cut is the closure of its sharp part, the
  points of the domain where the record is not continuous within its
  domain, so both are unique; a point outside the domain, such as a pole of
  `tan` or a non-real argument of `asin`, `acos` or `atan`, is never a jump.
  `NoCut`: no cut. `Logarithm`: the nonpositive real axis
  $(-\infty, 0]$, with jumps on $(-\infty, 0)$; the branch point 0 is
  outside the domain and in the closure of the jumps. `Root`: the same set
  and jumps, and the record is defined and continuous at the branch point 0.
  `RootFromDegreeTwo`: `Root` for a degree of at least 2, and no cut for
  degree 1. `asin`, `acos` and `atan` are real only, so their complex cuts
  lie outside their domain.
- **Closed side.** The side from which the record takes its value on its
  cut, the side reached when circling the branch point counterclockwise.
  `Above`: from above, the closed upper half-plane, the side of a cut along
  the negative real axis. `NoCut`: no cut, so no side.
- **Value on the cut.** The limit from the closed side at a point $u$ of
  the cut. `Logarithm`: $\ln \lvert u \rvert + \pi i$ at a negative real
  $u$, so $\log(-1) = \pi i$. `Root`:
  $\lvert u \rvert^{1/n} e^{i \pi / n}$ at a negative real $u$, for the
  degree $n$ of the call, which is 2 for `sqrt`, so
  $\sqrt{u} = i \sqrt{\lvert u \rvert}$ there. `NoCut`: no value on a cut.
- The closed side and the value on the cut apply on the cut that the cut
  slot gives at the degree of the call, so not for `rootn` of degree 1.
- **Principal range.** The values of the principal branch.
  `SingleValued`: the record has no branch to choose. `ClosedHalfPi`:
  $[-\pi/2, \pi/2]$. `ZeroToPi`: $[0, \pi]$. `OpenHalfPi`:
  $(-\pi/2, \pi/2)$. `LogarithmStrip`: the values $w$ with
  $-\pi \lt \mathrm{Im}\, w \le \pi$. `RootArgument`: 0 at 0, and otherwise
  the values whose argument lies in $(-\pi/n, \pi/n]$, for the degree $n$ of
  the call, which is 2 for `sqrt`.

### Special values and symmetries

| Record | At 0 | At 1 | At $-1$ | At $i$ | Value family | Quarter turns 0 to 3 |
| --- | --- | --- | --- | --- | --- | --- |
| `sin` | `Zero` | `NoValue` | `NoValue` | `NoValue` | `QuarterTurns` | `Zero`, `One`, `Zero`, `MinusOne` |
| `cos` | `One` | `NoValue` | `NoValue` | `NoValue` | `QuarterTurns` | `One`, `Zero`, `MinusOne`, `Zero` |
| `tan` | `Zero` | `NoValue` | `NoValue` | `NoValue` | `QuarterTurns` | `Zero`, `Undefined`, `Zero`, `Undefined` |
| `asin` | `ZeroPi` | `HalfPi` | `MinusHalfPi` | `NoValue` | `NoFamily` | `NoQuarterTurns` |
| `acos` | `HalfPi` | `ZeroPi` | `Pi` | `NoValue` | `NoFamily` | `NoQuarterTurns` |
| `atan` | `ZeroPi` | `QuarterPi` | `MinusQuarterPi` | `NoValue` | `NoFamily` | `NoQuarterTurns` |
| `exp` | `One` | `NoValue` | `NoValue` | `NoValue` | `NoFamily` | `NoQuarterTurns` |
| `log` | `NoValue` | `Zero` | `NoValue` | `NoValue` | `NoFamily` | `NoQuarterTurns` |
| `sqrt` | `Argument` | `Argument` | `NoValue` | `NoValue` | `PrincipalRoots` | `NoQuarterTurns` |
| `rootn` | `Argument` | `Argument` | `NoValue` | `NoValue` | `PrincipalRoots` | `NoQuarterTurns` |
| `abs` | `NoValue` | `NoValue` | `NoValue` | `One` | `Modulus` | `NoQuarterTurns` |

| Record | Undefined points | Period | Parity | Sign rules | Conjugate symmetry | Zeros and poles |
| --- | --- | --- | --- | --- | --- | --- |
| `sin` | `NoPoints` | `TwoPi` | `Odd` | `NoSignRule` | `OnDomain` | `MultiplesOfPi` |
| `cos` | `NoPoints` | `TwoPi` | `Even` | `NoSignRule` | `OnDomain` | `OddHalfPiMultiples` |
| `tan` | `OddHalfPiMultiples` | `Pi` | `Odd` | `NoSignRule` | `OnDomain` | `TangentZerosAndPoles` |
| `asin` | `BeyondOneOrImaginary` | `NoPeriod` | `Odd` | `NoSignRule` | `OnDomain` | `ZeroAtOrigin` |
| `acos` | `BeyondOneOrImaginary` | `NoPeriod` | `Reflection` | `NoSignRule` | `OnDomain` | `ZeroAtOne` |
| `atan` | `ImaginaryMultiples` | `NoPeriod` | `Odd` | `NoSignRule` | `OnDomain` | `ZeroAtOrigin` |
| `exp` | `NoPoints` | `TwoPiI` | `NoParity` | `NoSignRule` | `OnDomain` | `NoZeros` |
| `log` | `Zero` | `NoPeriod` | `NoParity` | `NoSignRule` | `OffCut` | `ZeroAtOne` |
| `sqrt` | `NoPoints` | `NoPeriod` | `NoParity` | `NoSignRule` | `OffCut` | `ZeroAtOrigin` |
| `rootn` | `ExcludedDegrees` | `NoPeriod` | `NoParity` | `NoSignRule` | `OffCut` | `ZeroAtOrigin` |
| `abs` | `NoPoints` | `NoPeriod` | `Even` | `Modulus` | `OnDomain` | `ZeroAtOrigin` |

- **Values at 0, 1, $-1$ and $i$.** The value of the record at an exact
  argument inside its domain, with the form in which it is built. `NoValue`:
  no registered value. `Zero` and `One`: the integers 0 and 1. `Argument`:
  the argument itself, which the roots return at their fixed points 0 and 1,
  for every degree. `ZeroPi`, `HalfPi`, `MinusHalfPi`, `Pi`, `QuarterPi` and
  `MinusQuarterPi`: $0 \pi$, $\pi/2$, $-\pi/2$, $\pi$, $\pi/4$ and
  $-\pi/4$, each the product of a rational and $\pi$, as the inverse
  trigonometric functions write every value, 0 as $0 \pi$. So the
  registered values are $\sin 0 = \tan 0 = 0$, $\cos 0 = \exp 0 = 1$,
  $\log 1 = 0$, $\sqrt{0} = 0$, $\sqrt{1} = 1$, $\mathrm{rootn}(0, n) = 0$,
  $\mathrm{rootn}(1, n) = 1$, `asin`, `acos` and `atan` at $-1$, 0 and 1,
  and $\lvert i \rvert = 1$. Values that DLMF tabulates elsewhere, such as
  $\sin(\pi/6) = 1/2$ or $\log(-1) = \pi i$, are not registered values.
- **Value family.** `NoFamily`: no family. `QuarterTurns`: the rational
  multiples $q \pi$ with an integer $2q$, whose value at the quarter turn
  $k = 2q \bmod 4$ is entry $k$ of the quarter-turn table. `PrincipalRoots`:
  the principal roots of rationals; degree 1 is the identity, and a rational
  root has its exact principal value. `Modulus`: $\lvert q \rvert$,
  $\lvert c \pi \rvert = \lvert c \rvert \pi$ and
  $\lvert c i \rvert = \lvert c \rvert$ for rationals $q$ and $c$.
- **Quarter-turn table.** The values at $k \pi/2$ for $k = 0, 1, 2, 3$:
  `Zero`, `One` and `MinusOne`, the integers, and `Undefined`, outside the
  domain. A record without the family `QuarterTurns` holds `NoQuarterTurns`
  at each of the four positions.
- **Undefined points.** The exact arguments outside the domain that the call
  constructor is planned to reject with `OutsideDomain`; they are domain
  facts, never values. `NoPoints`: none. `OddHalfPiMultiples`: $q \pi$ with
  $2q$ an odd integer. `BeyondOneOrImaginary`: a rational $q$ with
  $\lvert q \rvert \gt 1$, and $c i$ with a rational $c \ne 0$.
  `ImaginaryMultiples`: $c i$ with a rational $c \ne 0$. `Zero`: 0.
  `ExcludedDegrees`: a degree that is 0, a negative integer, a rational that
  is not an integer, $\pi$ or $i$.
- **Period.** `NoPeriod`, `TwoPi` ($2 \pi$), `Pi` ($\pi$) and `TwoPiI`
  ($2 \pi i$).
- **Parity.** `NoParity`: no parity and no reflection formula. `Odd`:
  $f(-u) = -f(u)$. `Even`: $f(-u) = f(u)$. `Reflection`:
  $f(-u) = \pi - f(u)$, the reflection formula
  $\arccos(-u) = \pi - \arccos u$.
- **Sign rules.** `NoSignRule`: none. `Modulus`: $\lvert u \rvert = u$ for a
  proved nonnegative $u$, and $\lvert u \rvert = -u$ for a proved
  nonpositive $u$.
- **Conjugate symmetry.** Where $f(\bar u) = \overline{f(u)}$ holds.
  `OnDomain`: at every argument of the domain, trivially for the real-only
  `asin`, `acos` and `atan`. `OffCut`: at every argument of the domain off
  the cut that the cut slot gives at the degree of the call; on the cut the
  value is that from the closed side, and its conjugate that from the other
  side.
- **Zeros and poles.** `MultiplesOfPi`: the zeros $k \pi$ for the integers
  $k$, and no pole. `OddHalfPiMultiples`: the zeros $q \pi$ with $2q$ an odd
  integer, and no pole. `TangentZerosAndPoles`: the zeros $k \pi$ and the
  simple poles $q \pi$ with $2q$ an odd integer, outside the domain.
  `ZeroAtOrigin` and `ZeroAtOne`: the one zero 0 or 1, and no pole.
  `NoZeros`: no zero and no pole. The branch point 0 of `log` and the roots
  is not a pole.

### Derivatives

| Record | Formula | Regions |
| --- | --- | --- |
| `sin` | `Cosine` | `Domain` |
| `cos` | `NegativeSine` | `Domain` |
| `tan` | `InverseCosineSquared` | `Domain` |
| `asin` | `Arcsine` | `RealOpenUnitInterval` |
| `acos` | `Arccosine` | `RealOpenUnitInterval` |
| `atan` | `Arctangent` | `RealLine` |
| `exp` | `Itself` | `Domain` |
| `log` | `Reciprocal` | `OffCutOrRealDomain` |
| `sqrt` | `RootPower` | `OffCutOrRealNonzero` |
| `rootn` | `RootPower` | `OffCutOrRealNonzero` |
| `abs` | `Sign` | `RealNonzero` |

- **Formula.** The derivative with respect to the operand $u$, as a template
  in $u$ and in the call itself, which differentiation multiplies by the
  derivative of $u$, the chain rule. `Cosine`: $\cos u$. `NegativeSine`:
  $-\sin u$. `InverseCosineSquared`: $\cos(u)^{-2}$. `Arcsine`:
  $1/\sqrt{1 - u^2}$. `Arccosine`: $-1/\sqrt{1 - u^2}$, both with the
  principal square root. `Arctangent`: $1/(1 + u^2)$. `Itself`: the call
  itself. `Reciprocal`: $u^{-1}$. `RootPower`:
  $(1/n) (\mathrm{rootn}(u, n)^{n - 1})^{-1}$ for the degree $n$ of the call,
  2 for `sqrt`, and 1 for degree 1. `Sign`: 1 for $u \gt 0$ and $-1$ for
  $u \lt 0$, built as the case split on the two half-lines of its region,
  which keeps the derivative formal at 0. The derivative with respect to the
  degree of `rootn` does not apply: a degree takes only natural values.
- **Regions.** One slot gives both regions where the formula holds: the
  holomorphic region and the region on real paths, along which the variable
  and the operand are proved real; elsewhere, at cuts, cusps and the edges
  of a region, the derivative stays formal. `Domain`: the whole domain on
  every path. `OffCutOrRealDomain`: off the cut on every path, and along real
  paths on the whole domain. `OffCutOrRealNonzero`: off the cut on every
  path, and along real paths at the nonzero operands, since the record is
  not differentiable at the branch point 0. `RealOpenUnitInterval`,
  `RealLine` and `RealNonzero`: along real paths only, on $(-1, 1)$, on the
  real line and at the nonzero operands; the holomorphic region of these is
  the empty set, a value of the slot. `RealNonzero` adds no condition of its
  own, since the case split of `Sign` leaves 0 out, so it is the region of
  the formula `Sign` and of no other.

### Series

| Record | Regular-point method | Expansion at a pole |
| --- | --- | --- |
| `sin` | `SineRecurrence` | `NoPoles` |
| `cos` | `CosineRecurrence` | `NoPoles` |
| `tan` | `TangentQuotient` | `TangentQuotient` |
| `asin` | `Empty` | `NoPoles` |
| `acos` | `Empty` | `NoPoles` |
| `atan` | `Empty` | `NoPoles` |
| `exp` | `ExponentialRecurrence` | `NoPoles` |
| `log` | `LogarithmIntegral` | `NoPoles` |
| `sqrt` | `RootComposition` | `NoPoles` |
| `rootn` | `RootComposition` | `NoPoles` |
| `abs` | `ModulusSign` | `NoPoles` |

- **Regular-point method.** How the truncated power series of a call is
  computed from the series of its operand at a regular point, one whose
  constant term $u_0$ is in the domain of the call and, for a record with a
  cut, off the cut: that is the validity condition of every method.
  `ExponentialRecurrence`: the recurrence
  $n f_n = \sum_k k u_k f_{n-k}$ of $f' = u' f$. `SineRecurrence` and
  `CosineRecurrence`: the coupled recurrences of $s' = u' c$ and
  $c' = -u' s$, giving $s$ or $c$. `LogarithmIntegral`: the value at $u_0$
  plus the integral of $u'/u$. `TangentQuotient`: the quotient of the sine
  and the cosine series. `RootComposition`: $\exp(\log(u)/n)$ for the degree
  $n$ of the call. `ModulusSign`: the series of $u$ for a constant term
  proved positive, and of $-u$ for one proved negative. The slot of `asin`,
  `acos` and `atan` is `Empty`, and the Taylor series of function
  expressions are planned to fill it in release 0.2.
- **Expansion at a pole.** `TangentQuotient`: the Laurent series of `tan` at
  a constant term where the cosine vanishes, the quotient of the sine and
  the cosine series. `NoPoles`: the record has no pole.
- The expansion at a branch point and the behaviour at $+\infty$ and
  $-\infty$ are in the [exemption list](#exemption-list).

### Numerical evaluation and connection rules

Every slot of these two groups is in the [exemption list](#exemption-list):
the enclosure kernel, the argument requirement, the Taylor-model eligibility
and the binary64 entry; the antiderivatives, the integration results, the
derivative-closed family, the summation, the equation inversion and the
limit rules.

### Other fields

| Record | Analyticity | Property inference |
| --- | --- | --- |
| `sin` | `Entire` | `RealOnReals` |
| `cos` | `Entire` | `RealOnReals` |
| `tan` | `Meromorphic` | `RealOnReals` |
| `asin` | `RealAnalyticOnOpenUnitInterval` | `RealValued` |
| `acos` | `RealAnalyticOnOpenUnitInterval` | `RealValued` |
| `atan` | `RealAnalyticOnReals` | `RealValued` |
| `exp` | `Entire` | `Exponential` |
| `log` | `OffCut` | `Logarithm` |
| `sqrt` | `OffCut` | `Root` |
| `rootn` | `OffCut` | `Root` |
| `abs` | `NotAnalytic` | `Modulus` |

- **Analyticity.** Where the record is analytic, and whether it is real on
  the real axis. `Entire`: holomorphic on the whole plane, and real on the
  real axis. `Meromorphic`: holomorphic on its domain, with poles outside
  it, and real on the reals of its domain. `RealAnalyticOnOpenUnitInterval`:
  real-analytic on $(-1, 1)$, and not at the ends of its domain.
  `RealAnalyticOnReals`: real-analytic on the real line. These two have no
  complex domain. `OffCut`: holomorphic on its domain off the cut that the
  cut slot gives at the degree of the call, so on the whole plane for
  `rootn` of degree 1, and real on the positive reals. `NotAnalytic`:
  holomorphic on no open set, and not real-analytic at 0.
- **Property inference.** The classes of the values of a call from the
  classes of its argument. `RealValued`: real on the whole domain.
  `RealOnReals`: real for a real argument. `Modulus`: 0 for a zero argument,
  positive for a nonzero argument and nonnegative for every argument.
  `Exponential`: positive for a real argument and nonzero for every
  argument. `Logarithm`: real for a positive argument. `Root`: imaginary for
  a negative argument, positive for a positive argument, nonnegative for a
  nonnegative argument and nonzero for a nonzero argument.
- The output names and the dimensions and angles are in the
  [exemption list](#exemption-list).

### Identity list

Knowledge that relates calls of several records, or nested calls, is kept
in the identity list `IDENTITIES`, not in a record. Each entry has an
identifier `FunctionIdentityId`, named like the entry, the records that it
names, its class and its condition. Its two sides are those that the table
states. The classes are:

- `Unconditional`: both sides have the same domain, and the entry needs no
  assumption, so the call constructor or the term core may apply it
  ([rules of the call constructor](../../architecture.md#rules-of-the-call-constructor)).
- `UnderAssumption`: the entry holds where its condition, an assumption
  about the operand, holds.
- `KeepsLeftDomain`: the left side is defined exactly where its condition
  holds, and the right side everywhere, so the entry keeps the domain of
  its left side as a condition.

| Entry | Statement | Class | Condition | Records |
| --- | --- | --- | --- | --- |
| `sqrt_eq_rootn` | $\mathrm{rootn}(u, 2) = \sqrt{u}$, for the literal degree 2 | `Unconditional` | `NoCondition` | `sqrt`, `rootn` |
| `rootn_one` | $\mathrm{rootn}(u, 1) = u$, for the literal degree 1 | `Unconditional` | `NoCondition` | `rootn` |
| `abs_abs` | $\lvert \lvert u \rvert \rvert = \lvert u \rvert$ | `Unconditional` | `NoCondition` | `abs` |
| `root_pow` | $\mathrm{rootn}(u, n)^k = u^{\lfloor k/n \rfloor} \mathrm{rootn}(u, n)^{k \bmod n}$ for a literal degree $n$ and every integer $k \ge 1$, with `sqrt` as the root of degree 2 | `Unconditional` | `NoCondition` | `sqrt`, `rootn` |
| `sqrt_sq` | $\sqrt{u^2} = \lvert u \rvert$ | `UnderAssumption` | `Real`: a real $u$ | `sqrt`, `abs` |
| `log_exp` | $\log(\exp u) = u$ | `UnderAssumption` | `PrincipalStrip`: $-\pi \lt \mathrm{Im}\, u \le \pi$ | `log`, `exp` |
| `exp_log` | $\exp(\log u) = u$ | `KeepsLeftDomain` | `Nonzero`: $u \ne 0$ | `exp`, `log` |
| `sin_asin` | $\sin(\arcsin u) = u$ | `KeepsLeftDomain` | `RealUnitInterval`: a real $u$ with $-1 \le u \le 1$ | `sin`, `asin` |
| `cos_acos` | $\cos(\arccos u) = u$ | `KeepsLeftDomain` | `RealUnitInterval`: a real $u$ with $-1 \le u \le 1$ | `cos`, `acos` |
| `tan_atan` | $\tan(\arctan u) = u$ | `KeepsLeftDomain` | `Real`: a real $u$ | `tan`, `atan` |

Every record is named by at least one entry. An entry names its records in
the first `count` positions of `records`, and the positions from `count` on
repeat the first record. The merge of exponentials,
$\exp a \exp b = \exp(a + b)$, and the inverse compositions in the other
direction, such as $\arcsin(\sin u) = u$, are not entries.

### Exemption list

The 15 slots of the list hold `Empty` for every record. Each is listed with
the release that is planned to fill it; a change of the list is reviewed
like a change of the meaning of the records.

| Group | Slot | Release | Planned with |
| --- | --- | --- | --- |
| Numerical slots and the binary64 entry | Enclosure kernel | 0.3 | numerical evaluation entries |
| Numerical slots and the binary64 entry | Argument requirement | 0.3 | numerical evaluation entries |
| Numerical slots and the binary64 entry | Taylor-model eligibility | 0.3 | numerical evaluation entries |
| Numerical slots and the binary64 entry | binary64 entry | 0.3 | binary64 scalars |
| Connection rules | Antiderivatives | 0.5 | indefinite integration |
| Connection rules | Integration results | 0.5 | indefinite and definite integration |
| Connection rules | Derivative-closed family | 0.5 | indefinite integration |
| Connection rules | Summation | 0.5 | sums and products |
| Connection rules | Equation inversion | 0.5 | transcendental equations |
| Connection rules | Limit rules | 0.5 | limits |
| Behaviour at infinity and at branch points | Expansion at a branch point | 0.5 | series beyond Taylor and Laurent |
| Behaviour at infinity and at branch points | Behaviour as the operand tends to $+\infty$ | 0.5 | series beyond Taylor and Laurent |
| Behaviour at infinity and at branch points | Behaviour as the operand tends to $-\infty$ | 0.5 | series beyond Taylor and Laurent |
| Output names, dimensions and angles | Output names | 0.7 | structured output |
| Output names, dimensions and angles | Dimensions and angles | 0.7 | quantity arithmetic and the settings context |

The list has these four groups only. Every other slot is filled for the
eleven records, but the regular-point method of `asin`, `acos` and `atan`,
which the [series](#series) state.

### Lookup and the entry

- **Lookup.** `lookup(name)` is a total function on byte slices: it returns
  the identifier of the record whose `length` equals the length of `name`
  and whose first `length` name bytes equal it, and `None` for every other
  slice, such as the empty name, a name longer than 8 bytes, a name that
  differs in case, or one that ends in zero bytes, such as `sin\0`, since
  the padding is not part of a name.
- **The entry.** `resolve(name, span)` returns the identifier that `lookup`
  gives, and for a name that the registry does not hold fails with
  `Fault(Syntax)` and the span `span` that its caller gives, such as the
  span of the name in the input. It looks in no other table.
- **No charges.** Neither takes a request context, and their work is
  bounded by the eleven records and the capacity of 8 bytes of a name.
  Access by identifier, `record`, `items` and `identity`, is an exhaustive
  `match` that returns a copy. None of them charges work: the registry has
  no charge point.

## Normative source

The normative source of definitions, notation, principal branches, branch
cuts and special values is the NIST Digital Library of Mathematical
Functions, Release 1.2.8 of 2026-09-15 (see [references](#references)). A
record follows DLMF except where a deviation is listed below.

| Record | DLMF sections |
| --- | --- |
| `sin`, `cos`, `tan` | 4.14 (definitions and periods), 4.16 (elementary properties), 4.17 (special values), 4.19 (Maclaurin series), 4.20 (derivatives), 4.21 (identities) |
| `asin`, `acos`, `atan` | 4.23(ii) (principal values), 4.23(iii) (reflection formulas), 4.23(vii) (special values), 4.24(i) (power series), 4.24(ii) (derivatives) |
| `exp` | 4.2(iii) (definition, series and period), 4.4(ii) (special values), 4.7(ii) (derivatives) |
| `log` | 4.2(i) (principal value and cut), 4.4(i) (special values), 4.6(i) (power series), 4.7(i) (derivatives), 4.8(i) (identities) |
| `sqrt`, `rootn` | 4.2(iv) (principal powers), 4.6(ii) (power series), 4.7(ii) (derivatives), 4.8(ii) (identities) |
| `abs` | 1.9(i) (modulus and phase) |

| Topic | DLMF | Library |
| --- | --- | --- |
| Names | $\ln$, $\arcsin$, $\arccos$, $\arctan$, $z^{1/2}$, $z^{1/n}$ and $\lvert z \rvert$ | `log`, `asin`, `acos`, `atan`, `sqrt`, `rootn` and `abs`; the names do not change the definitions |
| Values on a cut | The closed definition (4.2(i)) treats the cut as two sets of points, so the principal logarithm and powers are two-valued there, and the principal phase lies in $[-\pi, \pi]$ (1.9(i)) | One value: the limit from above, so $-\pi \lt \mathrm{Im} \log u \le \pi$, the single-valued principal phase that 1.9(i) and 4.2(i) also describe; there is no signed zero |
| Inverse trigonometric functions | Complex principal branches with cuts (4.23(ii)) | Real only: `asin` and `acos` on $[-1, 1]$ and `atan` on $\mathbb{R}$ |
| Poles and singular points | Tables list $\infty$ at poles, such as $\tan(\pi/2)$ (Table 4.17.1) | There are no infinite values: a pole, $\log 0$ and a root of degree 0 are outside the domain |
| Roots at zero | Powers are defined for $z \ne 0$ (4.2(iv)) | $\sqrt[n]{0} = 0$ for every degree $n \ge 1$, the continuous extension |

Two conventions follow DLMF but may surprise users: the root of a negative
real number is the principal value, so $\sqrt[3]{-8}$ is not $-2$, and the
modulus is not holomorphic, so $\lvert u \rvert$ has a derivative only on
real paths.

## Requirements

The requirement identifiers are those of the function registry of the
earlier implementation of the casξ computer algebra system; they are never
renumbered or reused. Each entry states the part of the requirement that the
records of kalyx meet, and the tests that are its evidence, in
`src/registry/tests.rs`; a name that starts with `items::` is that of a test
in the module `items` of that file.

### FUN-R01

**Lookup by name.** Lookup is total and the names are unique: every
registered name finds exactly one record, and a name that is not registered
finds none.

- **Implemented here.** `lookup`, `resolve` and the names of the records, as
  [lookup and the entry](#lookup-and-the-entry) state.
- **Evidence.** Positive: `lookup_finds_exactly_the_registered_names`, also
  through the entry, `names_are_unique_padded_identifiers` and
  `records_follow_the_keys_of_the_contract`. Negative:
  `unregistered_names_are_not_resolved`,
  `registered_names_are_not_reserved`, and
  `lookup_agrees_with_the_keys_on_a_name_corpus`, which looks up the
  registered names, 52 names of no record, the special forms, the reserved
  words, 400 edits of registered names and 400 random names, from the seed
  `0x5eed_f00d_0001`, through `lookup` and the entry.

### FUN-R02

**Call errors.** The number of arguments is checked first: a number other
than the arity of the record is a syntax error, which comes before the
domain check; with the right number of arguments, an argument outside the
domain is `OutsideDomain`; the degree of `rootn` is an ordinary argument,
and a degree that is not a positive integer is outside the domain.

- **Implemented here.** The part of the record: the arity and the argument
  roles of the [identity fields](#identity-fields), with the degree as an
  ordinary value argument, and the domain label `PositiveDegree`. The checks
  of a call are planned for the call constructor of the term core.
- **Evidence.** `only_rootn_takes_a_degree`; the labels in
  `items_are_those_of_the_contract`.

### FUN-R03

**Special values.** A registered special value is a value of the record at
a point inside its domain; a value assigned by convention outside the
domain is never registered, and an undefined point is a domain fact, never
a value.

- **Implemented here.** The values at 0, 1, $-1$ and $i$, the value
  families with the quarter-turn tables, and the undefined points of
  [special values and symmetries](#special-values-and-symmetries).
- **Evidence.** `items_are_those_of_the_contract`,
  `items::values_are_built_in_the_form_of_their_record` and
  `items::items_follow_the_records`.

### FUN-R04

**Derivative formulas.** Each record has a derivative formula with respect
to its operand on an open region of the holomorphic path, of real paths or
both, and no region holds a pole of `tan`, an end of the domain of `asin` or
`acos`, the cusp 0 of `abs` or, on the holomorphic path, a point of the cut
of `log`.

- **Implemented here.** The formula and the regions of
  [derivatives](#derivatives).
- **Evidence.** `items_are_those_of_the_contract` and
  `items::only_the_sign_formula_has_the_real_nonzero_region`.

### FUN-R05

**Domains and branch cuts.** The domain of each record is a condition that
holds exactly where it has a value; the cut is the closure of the points of
the domain where the record jumps; the value on the cut is the limit from
above; and each multivalued record takes its principal range.

- **Implemented here.** The domain labels with their conditions, the
  support, the cut, the closed side, the value on the cut and the principal
  range of [node, domain and branch cuts](#node-domain-and-branch-cuts).
- **Evidence.** `items_are_those_of_the_contract`,
  `items::sqrt_has_the_items_of_rootn_of_degree_two` and the negative
  example `log_value_on_the_cut_is_not_from_below`.

### FUN-R06

**Identities.** An identity relates calls of the records, with its
applicability class: unconditional, under assumptions, or keeping the
domain of its left side.

- **Implemented here.** The [identity list](#identity-list).
- **Evidence.** `identities_are_those_of_the_contract` and the negative
  example `exp_log_keeps_the_domain_of_its_left_side`.

### FUN-R07

**Admission to the verified set.** A registered fact enters the verified set
only with its proof. Planned with the upgrade to tier A3 in release 0.3; no
fact of the registry is verified yet.

## Deviations of the earlier implementation

The contract of the registry of the earlier implementation listed seven
deviations of its code from its rules. Four are corrected here, each with a
test that rejects it:

- **The cut, its side and its value.** The value on the cut and the
  principal range were not registry data, and the modules that read the
  cut decided it in their own code. They are slots now, with the closed side
  of the cut; `log_value_on_the_cut_is_not_from_below` rejects a value on
  the cut of `log` taken from below.
- **Relational knowledge.** The inverse compositions, $\exp(\log u)$,
  $\log(\exp u)$, $\lvert \lvert u \rvert \rvert$, $\sqrt{u^2}$ and the
  powers of roots were rules of the builder, without a list. They are
  entries of the identity list now, each with its class;
  `exp_log_keeps_the_domain_of_its_left_side` rejects
  $\exp(\log u) = u$ as an unconditional entry.
- **Other fields.** Analyticity did not exist, nor output names or
  dimensions and angles. Analyticity is filled for every record, and the
  other two are in the exemption list; `abs_is_not_analytic` rejects a
  missing analyticity and an analytic modulus.
- **Declared functions.** The earlier contract described a second table of
  declared functions to look in. Names resolve only against the registry
  now; `unregistered_names_are_not_resolved` checks that names a user might
  declare, such as `f`, `g` and `foo`, fail with `Syntax` at the entry, with
  the span of the caller.

The other three are corrected as part of later work, which is planned:

- **The degree of a root** was held only as an integer literal. The record
  gives the degree as an ordinary value argument; the call constructor of
  the term core is planned to check it by the class of its value.
- **Slots with markers.** Slots carried the markers *not implemented* and
  *not applicable*. Every slot is now filled or in the exemption list, the
  parity of `asin`, `acos`, `atan` and `abs` included, but the regular-point
  method of `asin`, `acos` and `atan`, which the Taylor series of function
  expressions are planned to fill.
- **No exemption list and no tests of completeness.** The exemption list is
  above; the completeness and consistency tests of the records are planned
  with function expressions.

## Testing obligations

1. **Records and names.** The order, names, arities and roles of the records
   are checked against the keys written out in the tests:
   `records_follow_the_keys_of_the_contract`,
   `names_are_unique_padded_identifiers` and `only_rootn_takes_a_degree`.
2. **Lookup.** Positive and negative examples of lookup and of the entry,
   with the span of the caller: `lookup_finds_exactly_the_registered_names`,
   `registered_names_are_not_reserved`,
   `lookup_agrees_with_the_keys_on_a_name_corpus` and
   `unregistered_names_are_not_resolved`.
3. **Slots.** Every slot of every record is compared with the tables of this
   contract, written out in the tests, and the number of records that fill
   each slot is counted: `items_are_those_of_the_contract`. The tests of the
   module `items` check the records against each other and against the
   documented meaning of their variants:
   `items::items_follow_the_records`,
   `items::values_are_built_in_the_form_of_their_record`,
   `items::sqrt_has_the_items_of_rootn_of_degree_two` and
   `items::only_the_sign_formula_has_the_real_nonzero_region`.
4. **Identity list.** `identities_are_those_of_the_contract` compares the
   entries with the table of this contract and checks that every record is
   named by an entry.
5. **Negative examples of the corrected deviations.**
   `log_value_on_the_cut_is_not_from_below`,
   `exp_log_keeps_the_domain_of_its_left_side`, `abs_is_not_analytic` and
   `unregistered_names_are_not_resolved`.
6. **No context.** `lookup_and_record_access_take_no_context` binds lookup,
   the entry and the three accessors to function types without a request
   context, and looks up one registered and one unregistered name through
   them.
7. **Independent evidence.** No test computes a function in binary64
   arithmetic or with the platform's mathematics library, and no test
   asserts the message of an error.

## Extractability

The registry is planned for tier A3 in release 0.3, so it is written in the
provable subset of Rust from its first change, as the
[architecture](../../architecture.md#verification-tiers) requires; no proof
target is registered for it yet, and none of its code has been extracted.
The subset is that of the krepi convention on the provable subset of Rust,
as [formal verification](../../formal-verification.md#provable-subset-and-design-rules)
cites it: the constructs R1 to R7, the provable design rules 1 to 9 and the
loop shapes.

- **Constructs.** No function item is passed as a value (R1), no
  `Iterator::any` (R2) or `Iterator::flatten` (R3) is called, no closure is
  given to a combinator or an adapter (R4), and no mutable borrow is taken
  (R5). The enumerations have names that are unique in kalyx: `FunctionId`,
  `FunctionRole`, the slot enumerations from `FunctionDomain` to
  `FunctionInference`, `FunctionIdentityId`, `FunctionIdentityClass` and
  `FunctionIdentityCondition` (R6). R7 concerns Lean code, which the
  component does not have.
- **Loop shapes.** `named` and `lookup` have one loop each, an index loop
  whose condition is a comparison and from which they return; neither uses
  `?`. Every other function is loopless.
- **Design rules.** Lookup and access read only the static tables and write
  nothing (1). Nothing is allocated, but the `String` of the message of the
  error of the entry (2). The records refer to each other only by
  identifier, and there is no `static mut` (3). The work of lookup is
  bounded by the eleven records and the 8 bytes of a name, and access has no
  loop (4). Every fact of a record is a field (5). The tables are private to
  the module, so only its accessors read them (6). The only `cfg` is
  `#[cfg(test)]` on the test module; the lint expectation of the module,
  which holds while no code outside it reads the registry, is selected by
  `cfg_attr` and changes no shape (7). There is no `Cell` or `RefCell` (8).
  The library forbids `unsafe` code (9).
- **External declarations.** An extraction needs the length and the
  indexing of byte slices and arrays, and `Error::new`, which copies its
  message into a `String`; the string literal of the message adds a
  `decide +native` axiom. The names of the records are zero-padded
  byte-string literals in a static table, the shape of the qualification
  case `registry-records`.

The module list of the component, the files that the `subset` step of
`cargo xtask check` checks against the provable subset and that
`cargo xtask formal check` inventories, holds the registry with its
directory:

```paths
src/registry.rs
src/registry
```

## Current deviations

None: the code and the tests follow every rule above.

## References

- F. W. J. Olver, A. B. Olde Daalhuis, D. W. Lozier, B. I. Schneider,
  R. F. Boisvert, C. W. Clark, B. R. Miller, B. V. Saunders, H. S. Cohl and
  M. A. McClain (eds.), *NIST Digital Library of Mathematical Functions*,
  [https://dlmf.nist.gov/](https://dlmf.nist.gov/), Release 1.2.8 of
  2026-09-15. Chapter 4 (elementary functions) and section 1.9 (complex
  numbers).
- W. Kahan, "Branch cuts for complex elementary functions, or much ado about
  nothing's sign bit", 1987 (placement of cuts and the side of continuity).
