# Exact numbers and the coefficient-field trait

This contract states the exact numbers of kalyx, arbitrary-size integers and
rationals, and the coefficient-field trait with its first implementation,
the field $\mathbb{Q}$ of rational numbers. It applies to the module
`src/number.rs` with its submodules `src/number/arithmetic.rs`,
`src/number/literal.rs` and `src/number/power.rs`, and to the module
`src/coefficient.rs`. The [architecture](../../architecture.md#coefficient-field-trait)
places the component among the foundations and states the design rules of the
trait, and the [public API conventions](../../conventions/public-api.md)
state the rules that every public interface follows. The limits and the
charges belong to the [context](../context/contract.md), and the errors to the
[errors and result states](../errors/contract.md).

**Status.** Implemented in `src/number.rs` and `src/coefficient.rs`, at tier
A0 (tested); the trait is planned for tier A2 in release 0.2. The first
caller in the library is the [term core](../terms/contract.md), whose numbers,
coefficients and constants are rationals; the
[polynomials](../polynomials/contract.md) over $\mathbb{Q}$ reach their
coefficients through the coefficient-field trait.

## Scope

- **Included.** Arbitrary-size integers (`Integer`) and canonical rationals
  (`Rational`): construction from machine integers, from a numerator and a
  denominator and from decimal literals; the arithmetic of rationals (sum,
  difference, product, quotient, negation, inverse, integer power and a
  charged comparison); display text and storage cost. The two layers of the
  coefficient-field trait, `CoefficientRing` and `CoefficientField`, the zero
  test answer `ZeroTest`, and the field of rationals `Rationals`.
- **Excluded, with their owners.**
  - The integer kernel (GCD, LCM, extended GCD, modular inverse, modular
    power, Chinese remaindering) and arithmetic on `Integer` itself: the
    coefficient fields of release 0.2. The reduction that num-rational does
    inside its own constructor is used, and is not an interface of kalyx.
  - The prime fields $\mathbb F_p$, the ring $\mathbb{Z}$ as a coefficient
    ring, $\mathbb{Q}(a)$, the result-state subtraits of rings that are not
    fields and maps between structures: the coefficient fields of release 0.2.
  - `PolynomialRing` and `Polynomial`: the
    [polynomials](../polynomials/contract.md).
  - Expressions and symbols: the [term core](../terms/contract.md). Spans
    of parsed expressions and the decimal literal syntax beyond one literal:
    the [parser](../syntax/contract.md), which reads each literal through
    `literal_at`.
  - Number theory: release 0.4.

## Interface

The module `kalyx::number` holds:

- `Integer`, with `From<i64>`, `From<u64>`, `bits()`, `is_zero()`,
  `is_positive()`, `is_negative()`, `Clone`, `Debug`, `Default` (zero),
  `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash` and `Display`;
- `Rational`, with `Rational::new(numerator, denominator, context)`,
  `Rational::parse_decimal(source, context)`, `From<Integer>`, `From<i64>`,
  the accessors `numerator()`, `denominator()`, `is_zero()`, `is_positive()`,
  `is_negative()` and `is_integer()`, the operations `add`, `subtract`,
  `multiply`, `divide`, `negate`, `inverse`, `power` and `compare`, each with
  the context last, and `Clone`, `Debug`, `PartialEq`, `Eq`, `Hash`,
  `Display` and `StorageCost`; it implements neither `PartialOrd` nor `Ord`.

The module `kalyx::coefficient` holds `ZeroTest<U>`, the traits
`CoefficientRing` and `CoefficientField`, and `Rationals`.

Crate-internal: `Rational::literal_at(text, offset, context)`, the literal
conversion for the parser, whose errors carry spans shifted by `offset`;
`Integer::magnitude_u64`, the absolute value of an integer as a `u64`, or
`None` beyond 64 bits, with which the term core reads an integer exponent for
the parser;
`Rational::binary(other, operation, span, context)`, the binary operations
with the caller's span on the error; and the kernels of `arithmetic`, `power`
and `literal`.

The crate root re-exports nothing of the component. No type of num-bigint,
num-rational or num-traits appears in a public signature or is re-exported,
and no public constructor takes the parts of a rational unchecked: the
`compile_fail` documentation tests of `Rational` check that `new_raw` does not
exist (`E0599`) and that a num-rational value does not convert into a
`Rational` (`E0277`). A third checks that rationals have no comparison
operators (`E0369`).

## Rules

### Types and invariants

- **Integer.** An integer of any size, with private contents. `bits()` is the
  bit length $\lvert x \rvert$ of the absolute value: 0 for zero, otherwise
  $\lfloor \log_2 \lvert x \rvert \rfloor + 1$. Integers are not checked
  against `max_integer_bits` when they are built from machine integers, since
  those have at most 64 bits; the operations of `Rational` check them when
  they use them.
- **Rational.** A numerator and a denominator with no common factor and a
  positive denominator; zero is $0/1$. Every public way to build a rational
  establishes this form, so two rationals are equal exactly when their values
  are, and the derived `PartialEq`, `Eq` and `Hash` compare values
  ([convention 14](../../conventions/public-api.md#14-canonical-representation-and-equality)).
  The bits of a rational are the larger bit length of its parts, at least 1.
- **Size.** Every rational that an operation returns has at most
  `max_integer_bits` bits. A rational built under one context and used under
  another is checked against the limits of the receiving context wherever an
  operation checks a bound: its bits are part of every bound below, and
  `compare` checks them only where it forms cross products, as Comparison
  under [checks and charges](#checks-and-charges) states.

### Decimal literals

`Rational::parse_decimal(source, context)` reads one literal of the form
`digit+ ('.' digit+)?` with ASCII digits: no sign, no exponent, no leading or
trailing point and no spaces. A literal with $k$ digits after the point is its
digits read as an integer over $10^k$, reduced, so `0.1` is $1/10$ and
`0.1 + 0.2` is exactly $3/10$; leading and trailing zeros do not change the
value.

1. The text is scanned without allocating. Text that is not a literal fails
   with `Fault(Syntax)` and the span of its first offending character, or an
   empty span at the end of the text when a digit is missing, as for the
   empty text and `1.`.
2. With $D$ digits, leading zeros included, the bound $4 D$ is checked with
   `check(IntegerBits, 4 D)`; $10^D - 1 \lt 16^D$, so the numerator and the
   denominator have at most $4 D$ bits.
3. $D$ work units are charged.
4. The value is converted and reduced.

The crate-internal `literal_at(text, offset, context)` does the same for a
literal at byte `offset` of a larger source: a syntax error carries the span
of the offending character shifted by `offset`, and a limit carries the span
of the whole literal.

### Checks and charges

Every operation that builds a rational runs in this order: the domain test,
where the operation has one; the check of a bound on the bits of its result
against `max_integer_bits`, computed from the operands alone; the charge,
whose amount depends only on the operands; the computation; and the check of
the bits of the result. A rejected operation therefore charges nothing,
allocates nothing but its error and leaves `work_used` unchanged. The bound
of each operation that builds a rational is at least the bits of every
operand, so an operand above the limit of the receiving context is rejected,
and at least the bits of every intermediate integer, so no integer that the
operation computes exceeds it; `parse_decimal` also copies its digits, one
byte per digit. `compare` builds no rational and checks its bound only on
the path of the cross products, as **Comparison** below states: on its other
paths an operand above the limit is not rejected, and aligning binary points
may compute an integer longer than the limit.
Write $\lvert x \rvert$ for
the bit length, the operands as $a/b$ and $c/d$, and $m = \lvert e \rvert$ for
an exponent $e$.

| Operation | Domain test | Bit bound | Charge |
| --- | --- | --- | --- |
| `new(n, d)` | $d = 0$ | $\max(\lvert n \rvert, \lvert d \rvert)$ | 1 |
| `parse_decimal` | syntax | $4 D$ | $D$ |
| `add`, `subtract` | none | $\max(\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert) + 1, \lvert b \rvert + \lvert d \rvert)$ | 1 |
| `compare` | none | only for the cross products: $\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert)$ | 1 |
| `multiply` | none | $\max(\lvert a \rvert + \lvert c \rvert, \lvert b \rvert + \lvert d \rvert)$ | 1 |
| `divide` | $c = 0$ | $\max(\lvert a \rvert + \lvert d \rvert, \lvert b \rvert + \lvert c \rvert)$ | 1 |
| `negate` | none | $\max(\lvert a \rvert, \lvert b \rvert)$ | 1 |
| `inverse` | $a = 0$ | $\max(\lvert a \rvert, \lvert b \rvert)$ | 1 |
| `power(e)` | $m \le$ `max_exponent`, then $a = 0$ with $e \lt 0$ | $\max(P(a, m), P(b, m), \lvert a \rvert, \lvert b \rvert)$ | $1 + \lvert m \rvert + w(m)$ |

- **Sums, products and quotients.** These are the bounds of the earlier
  implementation (FLD-R12). They bound the parts of the unreduced result, and
  reduction never lengthens a part. A bound above the limit is rejected even
  when the reduced result would fit: $1 + 1$ needs 3 bits.
- **Powers.** The exponent is checked first, with
  `check(Exponent, m)`, so a zero base with an exponent beyond `max_exponent`
  reports the limit. $P(x, m)$ is an upper bound of the bits of $x^m$: 1 for
  $m = 0$, 0 for $x = 0$ and $m \ge 1$, and otherwise the smaller of
  $m \lvert x \rvert + 1$, the estimate of the earlier implementation
  (FLD-R03), and $\lfloor m L / 2^{32} \rfloor + m s + 1$, where
  $x \le u \cdot 2^s$ with $u$ the value of $x$ when it has at most 64 bits
  ($s = 0$), and otherwise its leading 64 bits, plus one unless the bits
  below them are all zero, and $L / 2^{32} \ge \log_2 u$ is a fixed-point
  upper bound with 32 fractional bits, computed with machine integers by
  repeated squaring rounded up, and exact when $u$ is a power of two. $P$ is
  computed without allocating. For every $m$ it is exact when $x$ is a power
  of two and never above the estimate; for $m \lt 2^{31}$ it is at most one
  bit above the bits of $x^m$. The bits of the base are part of the bound, so
  a base above the receiving limit is rejected even for $m = 0$; for
  $m \ge 1$ they never exceed $P$. A bound that does not fit in a `u64`
  exceeds every limit, even `u64::MAX`, and is reported with
  `LimitAmount::Bound(u64::MAX)`. Under the default limits $2^{4095}$, of
  4096 bits, is returned and $2^{4096}$ is rejected. The charge counts the
  operation, the bit length $\lvert m \rvert$ of $m$ and the number $w(m)$ of
  its one bits: the squarings and multiplications of binary powering, which
  computes the numerator and the denominator separately. The parts of a
  canonical base are coprime, so their powers need no reduction.
- **Comparison.** `compare` builds no rational and never forms the
  difference. It takes the first of these paths that applies, chosen from
  the parts without allocating: equal parts, which give `Equal`; different
  signs; two power-of-two denominators $2^p$ and $2^q$, by aligning the
  binary points; equal denominators, by the numerators; sums of bit lengths
  $\lvert a \rvert + \lvert d \rvert$ and $\lvert c \rvert + \lvert b \rvert$
  that differ by at least two, which decide, since $\lvert u v \rvert$ is
  $\lvert u \rvert + \lvert v \rvert - 1$ or $\lvert u \rvert + \lvert v \rvert$
  for nonzero $u$ and $v$; and otherwise the cross products $a d$ and
  $c b$. Only the last path forms products, and only it checks a bound:
  that of the table, which neither cross product exceeds. So `compare`
  fails with `ResourceLimit` naming `max_integer_bits`, with
  `LimitAmount::Required` of the bound and before the charge, exactly when
  it needs the cross products and their bound exceeds the limit. Every path
  then charges one unit before it compares, so a pair charges the same
  under every limit that admits it. Aligning the binary points is not
  checked: for $p \gt q$ it shifts $c$ to $\lvert c \rvert + p - q$ bits,
  fewer than the bound of the cross products, which is at least
  $\lvert c \rvert + p + 1$. The shifted numerator is not bounded by
  `max_integer_bits`: for operands within the limit it has fewer than twice
  `max_integer_bits` bits, so under the default limits $2^{-4095}$ and
  $2^{4096} - 1$ shift the latter to 8191 bits, and for operands above the
  limit it is longer still: under `max_integer_bits` 0, $2^{100000}$ and
  $2^{-100000}$ shift the former to 200,001 bits. Two equal rationals
  therefore compare `Equal` under every `max_integer_bits`, though the
  charge still observes `max_work`, cancellation and the deadline, and an
  operand above the receiving limit is checked only where it takes part in
  cross products.
  With $N = 2^{2048}$, under the default limits $E = (N + 1)/(N - 1)$, of
  2049 and 2048 bits, compares `Equal` with itself, though its difference
  with itself needs 4098 bits and is rejected; $(N - 1)/(N - 3)$ and
  $(N - 3)/(N - 5)$ need 4096 bits and are ordered; and $E$ and
  $(N - 1)/(N - 3)$ need 4097 bits and are rejected. The cross products of
  $-E$ and $(N - 1)/(N - 3)$ would need 4097 bits too, but their signs
  order them; so do the binary points of $(2^{2047} + 1)/2^{2047}$ and
  $(2^{2048} + 1)/2^{2048}$, whose cross products would also need 4097
  bits. $E$ and $(N - 3)/(N + 3)$, whose sums of bit lengths 4098 and 4096
  differ by exactly two, are ordered by these sums, though 4098 exceeds the
  limit.
- **The result check.** The bits of every result are checked with
  `check(IntegerBits, bits)` as in the earlier implementation; since every
  bound is at least the bits of the result, the check fails only if a bound
  is wrong.
- **Spans.** The public entries other than `parse_decimal` put no span on
  their errors. `parse_decimal` reports spans as `literal_at` does with
  offset 0: the offending character on a syntax error, and the whole literal
  on a limit or on a failed charge. The crate-internal entries put the
  caller's span on the domain error, the checks and the charge.

### Fast paths

The results do not depend on the path. Integer operands keep the denominator
1 without a reduction; an integer quotient by $\pm 1$ negates or copies.
When both denominators are powers of two, sums, differences, products and
quotients by $\pm 2^k$ count trailing zero bits instead of a GCD. Other sums
use the split $b = g u$, $d = g v$ with $g = \gcd(b, d)$, where only
$\gcd(a v \pm c u, g)$ remains to cancel; other products cancel
$\gcd(a, d)$ and $\gcd(c, b)$, and a quotient multiplies by the inverse of
the divisor. All GCDs are those of the reduction inside num-rational. Every
path charges the same amount.

### Division by zero

`divide` by zero, `inverse` of zero, `new` with a zero denominator and a zero
base with a negative exponent fail with `Fault(DivisionByZero)`. The zero test
comes before any check of `max_integer_bits` and before any charge, so the
error is the same under every limit and every remaining work, and nothing is
charged; only the exponent check of a power comes first.

### Storage

`StorageCost` for a rational $n/d$ is one node and
$\lvert n \rvert + \lvert d \rvert + 3$ bytes, the formula of the
[context](../context/contract.md#storage-costs), saturating at `u64::MAX`.
Zero costs $(1, 4)$. The `measure` of `Rationals` is the same formula; it
takes constant time, since the bit lengths are read from the stored
integers.

### Display, order and equality

- **Display.** An integer is its decimal digits with a leading `-` when
  negative. A rational is its numerator, followed by `/` and its denominator
  unless the denominator is 1: `-3/4`, `5`, `0`. The text is deterministic and
  depends only on the value. As
  [convention 10](../../conventions/public-api.md#10-bounded-output) states,
  `Display` is a debugging convenience and takes no context.
- **Debug.** The stored numerator and denominator, which the canonical form
  makes unique.
- **Order.** The charged `compare` is the only order of rationals: a
  comparison may form cross products of up to
  $\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert)$
  bits, so, as
  [convention 1](../../conventions/public-api.md#1-request-context-last)
  asks of every public method that may allocate, it takes the context. The
  total order of the
  [term core](../terms/contract.md#kinds-and-the-total-order) compares
  numbers by value through it, so that each step is charged; equal numbers
  have equal parts, so they never make the order of terms or `Term::equals`
  exceed `max_integer_bits`. `Rational`
  implements neither `PartialOrd` nor `Ord`, and is not a key of ordered
  collections. `Integer` keeps its derived order: comparing two integers
  reads their digits and does not allocate.

### The coefficient-field trait

- **Shape.** As the [architecture](../../architecture.md#coefficient-field-trait)
  states: `CoefficientRing` with the associated types `Element: Clone` and
  `Undecided` and the methods `same_parent`, `zero`, `one`, `from_integer`,
  `negate`, `add`, `subtract`, `multiply`, `zero_test` and `measure`, and
  `CoefficientField: CoefficientRing` with `inverse` and `divide`. Every
  method takes the parent structure as `&self`; every method but `measure`
  takes the context last and returns a `Result`.
- **Storage cost.** `measure(&self, a)` returns the cost of the element `a`
  as a `Storage`, its nodes and logical bytes by the storage rules of the
  [context](../context/contract.md#storage-costs). The cost depends only on
  the parent and the element; `measure` takes no context, charges nothing
  and cannot fail, as `StorageCost` does. An element whose cost cannot be
  computed in constant time keeps its cost from when it was built, and
  `measure` reads it. Code generic over the trait, such as the shared
  algorithms of the [polynomials](../polynomials/contract.md), takes the
  costs of coefficients only from `measure`, and every later coefficient
  field implements it with a formula of its own.
- **Sealing.** Both traits have the supertrait `Sealed` of a private module,
  so only kalyx implements them, until 1.0, and later releases can add
  required methods without breaking callers. The `compile_fail` documentation
  test of `CoefficientRing` checks that a type outside the library cannot
  implement it even with every method (`E0603`).
- **No default methods.** Neither trait has a default method, so no
  implementation calls a default method on `self`; the parents have no
  lifetime parameters, and no method takes a closure.
- **`ZeroTest`.** `Zero`, `Nonzero` or `Undecided(U)`. It is the registered
  exception to [convention 3](../../conventions/public-api.md#3-extensible-enums-and-records):
  its three cases are complete, so it is not `#[non_exhaustive]`. A decided
  answer is correct.
- **Receiver rule.** The methods assume that their elements belong to
  `self`; `same_parent` is checked only where a parent and an element are
  stored together.
- **Charging.** Each element operation checks the sizes of its result before
  it works and charges for itself, with an amount that depends only on its
  operands.
- **Zero test first.** In a field whose zero test is structural, `inverse`
  and `divide` test the element or the divisor for zero before any charge of
  the operation, and fail with `Fault(DivisionByZero)`; a field whose zero
  test is charged pays for the test first.

### Rationals

`Rationals` is a zero-sized parent, with `Clone`, `Copy`, `Debug`, `Default`,
`PartialEq`, `Eq` and `Hash`. Its `Element` is `Rational` and its
`Undecided` is `std::convert::Infallible`.

- `negate`, `add`, `subtract`, `multiply`, `inverse` and `divide` are the
  operations of `Rational`, with their checks and charges.
- `zero`, `one` and `from_integer` check the bits of the new element, at
  least 1, against `max_integer_bits`, then charge one unit, and only then
  build the element, so a rejected element builds nothing but its error.
- `same_parent` is always `true`, and `zero_test` reads the numerator and
  always decides. Both take constant time, allocate nothing and charge
  nothing.
- `measure` is the storage cost of a rational, one node and
  $\lvert n \rvert + \lvert d \rvert + 3$ bytes for $n/d$, the value of
  `StorageCost` of `Rational`, which `Rational` keeps implementing.

## Requirements

The requirement identifiers are those of the coefficient fields of the
earlier implementation of the casξ computer algebra system; they are never
renumbered or reused. Each entry states the part of the requirement that
applies to the rationals and to the trait, as kalyx implements it, and the
tests that are its evidence. Tests are in `tests/numbers.rs` unless the entry
names `tests/coefficient.rs` or a file below `src/number/`. The bit check of
an integer is [CTX-R07](../context/contract.md#ctx-r07) of the context.

### FLD-R01

**Canonical forms.** A rational is a reduced fraction of an integer numerator
and a positive denominator, zero being $0/1$. Two canonical forms are equal
exactly when they denote the same number, and every rational has one; every
operation returns one.

- **Implemented here.** The private fields of `Rational`, the reduction of
  `new` and of the kernels, and the fast paths, which build a fraction without
  a reduction only where it is canonical by construction.
- **Evidence.** Positive: `rationals_are_canonical_and_displayed_deterministically`.
  Negative: `canonical_values_match_the_general_reduction` in
  `src/number/dyadic_tests.rs`, with unreduced inputs and negative
  denominators. Also `rationals_have_unique_canonical_forms` in
  `tests/coefficient.rs`, `ex1_sums_are_reduced_to_lowest_terms`,
  `rational_operations_match_small_integer_oracle`,
  `integer_and_mixed_paths_match_independent_exact_answers`, which evaluates
  the 518 rows of `tests/fixtures/integer_paths.tsv` at word boundaries of
  31 to 1024 bits and compares both parts (the fixture is plain TSV with its
  header row on line 1, as `tests/fixtures/README.md` states, and
  `integer_paths_fixture_rejects_a_missing_commented_or_late_header`,
  `integer_paths_fixture_rejects_comment_and_empty_lines_after_the_header`
  and `integer_paths_fixture_rejects_a_row_of_five_columns_and_a_duplicate_id`
  check its format), and in
  `src/number/dyadic_tests.rs`
  `normalization_removes_exactly_the_shared_powers_of_two`,
  `ring_operations_match_the_general_reduction`,
  `unreduced_dyadic_operands_still_produce_canonical_values`,
  `division_by_a_signed_power_of_two_matches_the_general_quotient` and
  `other_operands_use_the_general_path`.

### FLD-R02

**Division and inverse.** A zero divisor, or a zero element to invert, is the
domain error `DivisionByZero`; otherwise the result is the quotient or the
inverse, whose product with the element is 1. kalyx strengthens the priority:
the zero test comes before every size check and every charge, so a zero
divisor is `DivisionByZero` in every state of the context and charges
nothing.

- **Implemented here.** `Rational::new`, `divide`, `inverse` and `power`, and
  `inverse` and `divide` of `Rationals`.
- **Evidence.** Positive: `rationals_have_inverses_and_zero_has_none` in
  `tests/coefficient.rs`. Negative: `division_by_zero_fails_before_any_charge`,
  with no work left and a bit limit of 0. Also
  `integer_halving_and_zero_divisors_keep_their_results_and_errors` in
  `src/number/dyadic_tests.rs` and
  `integer_paths_still_observe_work_cancellation_and_errors`.

### FLD-R03

**Integer powers.** $a^0 = 1$ for every $a$, including $0^0 = 1$, and every
negative power of zero is `DivisionByZero`. An exponent whose absolute value
is above `max_exponent` fails with `ResourceLimit` naming it, before the zero
test. The bits of the result are checked with the bound $P$ of
[checks and charges](#checks-and-charges), which is never above the estimate
$\lvert e \rvert \cdot \mathit{bits}(a) + 1$ for any exponent. The check
also covers the bits of the base, so $a^0$ fails when $a$ has more than
`max_integer_bits` bits; for $e \ne 0$ the estimate covers them, so a power
whose estimate is within `max_integer_bits` is returned when the charge
succeeds.

- **Implemented here.** `Rational::power`, with `power_bits`,
  `power_charge` and `power_part` of `src/number/power.rs`.
- **Evidence.** Positive: `ex3_integer_powers_use_the_empty_product`.
  Negative: `the_power_checks_the_exponent_then_the_zero_base_then_the_bits`.
  Also `a_power_beyond_max_integer_bits_is_rejected_before_any_charge`,
  `power_bound_is_exact_for_powers_of_two_at_the_default_bit_limit`,
  `computational_growth_is_bounded`, `ex5_growth_is_checked_before_arithmetic`,
  and in `src/number/power.rs` `the_power_bound_is_exact_within_one_bit`,
  `the_power_bound_is_exact_for_powers_of_two_and_holds_for_wide_bases`,
  `the_power_bound_holds_its_claims_for_large_exponents`,
  `the_power_bound_holds_where_the_last_unit_of_the_logarithm_decides`,
  `the_power_bound_can_be_two_bits_above_just_below_2_pow_32` and
  `binary_powering_matches_repeated_products`.

### FLD-R04

**Zero tests.** A zero test answers zero, nonzero or undecided; the zero test
of the rationals is exact and never undecided, which its reason type
`Infallible` makes impossible.

- **Implemented here.** `zero_test` of `Rationals`.
- **Evidence.** Positive: `rationals_decide_every_zero_test_without_a_charge`
  in `tests/coefficient.rs`. Negative: `rationals_have_inverses_and_zero_has_none`
  in `tests/coefficient.rs`, which checks that the test answers zero exactly
  for the zero of the model.

### FLD-R12

**Accounting under the request context.** The effect of every operation on
the context is a sequence of charges that stops at the first failure; the
amounts depend only on the operands. The bit bounds of the rationals are the
closed forms of [checks and charges](#checks-and-charges); a bound above
`max_integer_bits` fails with `ResourceLimit` naming `max_integer_bits`, and
in kalyx it does so before the charge, so the work is unchanged. Under limits
at or above the bound, with work left and without a deadline or
cancellation, the value is returned.

- **Implemented here.** Every operation of `Rational` and of `Rationals`.
- **Evidence.** Positive: `operations_charge_one_unit_and_powers_by_their_exponent`.
  Negative: `an_addition_beyond_max_integer_bits_is_rejected_before_any_charge`,
  `a_multiplication_beyond_max_integer_bits_is_rejected_before_any_charge`
  and `a_power_beyond_max_integer_bits_is_rejected_before_any_charge`. Also
  `a_sum_whose_denominators_dominate_is_rejected_before_any_charge`,
  `a_quotient_is_bounded_by_its_crossed_parts`,
  `integer_shortcuts_keep_conservative_growth_checks`,
  `operands_are_checked_against_the_receiving_limits`,
  `deadline_and_exhausted_budget_prevent_results`,
  `integer_paths_still_observe_work_cancellation_and_errors`,
  `literals_charge_one_unit_per_digit_after_the_bit_check`,
  `rationals_are_ordered_by_value`,
  `equal_rationals_compare_equal_where_their_difference_is_rejected`,
  `each_path_of_the_comparison_charges_one_unit_under_every_admitting_limit`,
  `only_cross_products_beyond_max_integer_bits_are_rejected`,
  `terms_with_equal_numbers_beyond_half_the_bit_limit_are_equal` in
  `tests/terms.rs`,
  `the_value_of_rational_sum_1024_equals_its_answer_under_the_default_limits`
  in `tests/command.rs`, `rationals_check_and_charge_new_elements`
  and `rationals_measure_their_elements_by_the_storage_formula` in
  `tests/coefficient.rs`, and in `src/number/positive_compare_tests.rs`
  `the_comparison_takes_the_first_path_that_applies`,
  `positive_comparison_matches_an_independent_small_integer_oracle`,
  `equal_adjacent_and_disjoint_product_bit_ranges_remain_exact`,
  `hundred_thousand_bit_widths_check_only_the_bound_of_the_cross_products` and
  `positive_comparison_preserves_every_small_bit_work_boundary_and_priority`.

### Literals, without an identifier

The literals have no requirement identifier of the earlier implementation;
the rule is stated under [decimal literals](#decimal-literals).

- **Evidence.** Positive: `decimal_literals_add_exactly` and
  `ex2_decimal_literals_are_exact_rationals`. Negative:
  `malformed_decimal_literals_are_syntax_errors_with_spans`. Also
  `literals_reserve_four_bits_per_decimal_digit`,
  `literal_word_boundaries_preserve_values_and_input_growth_limits`,
  `literals_charge_one_unit_per_digit_after_the_bit_check`, and in
  `src/number/literal.rs`
  `a_literal_inside_a_larger_source_reports_shifted_spans` and
  `small_and_large_digit_strings_convert_alike`.

## Testing obligations

1. **Requirements.** One positive and one negative test per requirement, as
   each entry above names them.
2. **Bounds before charges.** For an addition, a multiplication and a power,
   a test whose bound exceeds `max_integer_bits` checks `ResourceLimit` with
   `LimitId::Field(LimitField::IntegerBits)` and an unchanged `work_used`.
3. **Field properties.** `tests/coefficient.rs` states associativity,
   commutativity, distributivity, inverses and canonical uniqueness once,
   generically over `K: CoefficientField` and a model of the field written in
   the test, and instantiates them with `Rationals`. Each family runs 1,000
   cases from a fixed seed of a SplitMix64 generator written in the test,
   compared with a model of $\mathbb{Q}$ as reduced `i128` fractions with their
   own GCD, on operands of at most 16 bits so that the model never
   overflows, and 50 cases with operands of about 256 bits, checked by the
   identities of the trait alone. The generator samples zero, small and
   larger integers, power-of-two denominators and general fractions.
4. **No message text.** No test asserts the message of an error; tests
   compare the kind, the span and the exceeded limit.
5. **Work.** Tests assert the amounts that this contract fixes, and that a
   rejected operation charges nothing; they assert no other amount.

## Extractability

The trait is shaped for extraction as the architecture requires: associated
types and `&self` methods, no default methods, no lifetime parameters on the
parents and no closures. The numbers are not written in the provable subset:
they allocate through num-bigint and num-rational, whose operations are
outside the subset and would be trusted external functions, and the literal
scanner iterates over characters. The kernels of `src/number/arithmetic.rs`
and `src/number/power.rs` use `match` instead of combinators with closures
and instead of `if let`, and have at most one loop each; `log2_upper` in
`src/number/power.rs` is a `const fn` over machine integers. No proof target
is registered for this component.

The module list of the component, the files that the `subset` step of
`cargo xtask check` checks against the provable subset and that
`cargo xtask formal check` inventories, holds the coefficient-field trait
alone; the numbers are not listed:

```paths
src/coefficient.rs
```

## Current deviations

None: the code and the tests follow every rule above.
