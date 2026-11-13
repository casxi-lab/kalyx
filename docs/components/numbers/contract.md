# Exact numbers and the coefficient-field trait

This contract states the exact numbers of kalyx, arbitrary-size integers and
rationals, with the integer kernel, and the coefficient-field trait with its
implementations, the field $\mathbb{Q}$ of rational numbers and the prime
fields $\mathbb F_p$ of the primes $p \lt 2^{32}$. It applies to the module
`src/number.rs` with its submodules `src/number/arithmetic.rs`,
`src/number/integer.rs`, `src/number/literal.rs` and `src/number/power.rs`,
and to the module `src/coefficient.rs` with its submodules
`src/coefficient/prime.rs` and `src/coefficient/prime/traits.rs`. The
[architecture](../../architecture.md#coefficient-field-trait) places the
component among the foundations and states the design rules of the trait,
and the [public API conventions](../../conventions/public-api.md) state the
rules that every public interface follows. The limits and the charges belong
to the [context](../context/contract.md), and the errors to the
[errors and result states](../errors/contract.md).

**Status.** Implemented in `src/number.rs` and `src/coefficient.rs`, at tier
A0 (tested), with the integer kernel in `src/number/integer.rs` and the
prime fields in `src/coefficient/prime.rs` and its child
`src/coefficient/prime/traits.rs` at tier A1 (tested with a written
contract); the trait is planned for tier A2 in release 0.2. The
first caller in the library is the [term core](../terms/contract.md), whose
numbers, coefficients and constants are rationals; the
[polynomials](../polynomials/contract.md) over $\mathbb{Q}$ reach their
coefficients through the coefficient-field trait. The integer kernel has no
caller in the library yet but the prime fields, which have none themselves:
its first production caller is planned to be the GCD and the factorization
of polynomials over $\mathbb{Q}$, in release 0.2, and the first production
callers of the prime fields are planned to be the multimodular GCD over
$\mathbb{Q}$ and the Berlekamp factorization, in the same release. Chinese
remaindering is planned for tier A2 in release 0.4, and the kernel has no
A3 upgrade.

## Scope

- **Included.** Arbitrary-size integers (`Integer`) and canonical rationals
  (`Rational`): construction from machine integers, from a numerator and a
  denominator and from decimal literals; the arithmetic of rationals (sum,
  difference, product, quotient, negation, inverse, integer power and a
  charged comparison); display text and storage cost. The arithmetic of
  integers (sum, difference, product, negation, absolute value, Euclidean
  division and exact quotient) and the integer kernel: GCD, LCM, extended
  GCD, modular inverse, modular power, congruences and Chinese
  remaindering. The two layers of the coefficient-field trait,
  `CoefficientRing` and `CoefficientField`, the zero test answer
  `ZeroTest`, the field of rationals `Rationals`, and the prime fields
  `PrimeField` of the primes $p \lt 2^{32}$ with their elements
  `PrimeResidue`, whose constructor decides that the modulus is prime.
- **Excluded, with their owners.**
  - The GCDs of the reduction of rationals: the reduction that num-rational
    does inside its own constructor is used, and is not an interface of
    kalyx; the integer kernel takes no part in it.
  - The ring $\mathbb{Z}$ as a coefficient ring, the residue rings
    $\mathbb{Z}/n$, $\mathbb{Q}(a)$, the result-state subtraits of rings that
    are not fields, maps between structures, such as the reduction of
    integers and rationals into a prime field, and the comparison of the
    parents of two elements: the coefficient fields of release 0.2. The
    operations on the polynomials over a prime field beyond those of the
    [polynomials](../polynomials/contract.md), such as division with
    remainder, and the Berlekamp factorization: the basic polynomial
    algorithms over $\mathbb{Q}$, release 0.2. Prime fields of larger primes
    and extension fields: release 0.4.
  - `PolynomialRing` and `Polynomial`: the
    [polynomials](../polynomials/contract.md).
  - Expressions and symbols: the [term core](../terms/contract.md). Spans
    of parsed expressions and the decimal literal syntax beyond one literal:
    the [parser](../syntax/contract.md), which reads each literal through
    `literal_at`.
  - Number theory beyond the integer kernel, such as primality tests,
    factorization and combinatorics: release 0.4. The constructor of a prime
    field decides the primality of its modulus with a test of its own,
    which is not a public entry.

## Interface

The module `kalyx::number` holds:

- `Integer`, with `From<i64>`, `From<u64>`, `bits()`, `is_zero()`,
  `is_positive()`, `is_negative()`, the operations `add`, `subtract`,
  `multiply`, `negate`, `absolute`, `divide_with_remainder` and
  `exact_quotient`, each with the context last, `Clone`, `Debug`, `Default`
  (zero), `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Display` and
  `StorageCost`;
- the integer kernel: the functions `gcd(a, b, context)`,
  `lcm(a, b, context)`, `extended_gcd(a, b, context)`,
  `modular_inverse(a, modulus, context)`,
  `modular_power(base, exponent, modulus, context)` and
  `crt(congruences, context)`; `Congruence`, with
  `Congruence::new(residue, modulus, context)` and the accessors `residue()`
  and `modulus()`; the results `IntegerDivision` (`quotient()`,
  `remainder()`) and `IntegerBezout` (`gcd()`, `left()`, `right()`); and the
  outcomes `ExactQuotient` (`Quotient(q)` or `NotDivisible`),
  `ModularInverse` (`Inverse(v)` or `NonUnit(g)`) and `CrtResult`
  (`Solution(congruence)` or `Inconsistent`), which are `#[non_exhaustive]`.
  Each implements `Clone`, `Debug`, `PartialEq`, `Eq`, `Hash` and
  `StorageCost`, and `IntegerBezout`, `Congruence` and `CrtResult`
  implement `Display`;
- `Rational`, with `Rational::new(numerator, denominator, context)`,
  `Rational::parse_decimal(source, context)`, `From<Integer>`, `From<i64>`,
  the accessors `numerator()`, `denominator()`, `is_zero()`, `is_positive()`,
  `is_negative()` and `is_integer()`, the operations `add`, `subtract`,
  `multiply`, `divide`, `negate`, `inverse`, `power` and `compare`, each with
  the context last, and `Clone`, `Debug`, `PartialEq`, `Eq`, `Hash`,
  `Display` and `StorageCost`; it implements neither `PartialOrd` nor `Ord`.

The module `kalyx::coefficient` holds `ZeroTest<U>`, the traits
`CoefficientRing` and `CoefficientField`, `Rationals`, and the prime fields:
`PrimeField`, with `PrimeField::new(p, context)` and the accessor
`modulus()`, and `Clone`, `Copy`, `Debug`, `PartialEq`, `Eq` and `Hash`;
and its element `PrimeResidue`, with the accessor `value()`, and `Clone`,
`Copy` and `Debug`. Both implement the two coefficient traits through
`PrimeField`.

Crate-internal: `Rational::literal_at(text, offset, context)`, the literal
conversion for the parser, whose errors carry spans shifted by `offset`;
`Integer::magnitude_u64`, the absolute value of an integer as a `u64`, or
`None` beyond 64 bits, with which the term core reads an integer exponent for
the parser and `from_integer` of a prime field reads its remainder;
`Rational::binary(other, operation, span, context)`, the binary operations
with the caller's span on the error; `words(bits)`, the machine words
$\max(1, \lceil \mathit{bits} / 64 \rceil)$ by which the products, the
quotients and the powers of `Rational` and the integer kernel charge; and the
kernels of `arithmetic`, `power` and `literal`. The steps of the integer
kernel in `integer` are private to it.

The crate root re-exports nothing of the component. No type of num-bigint,
num-rational or num-traits appears in a public signature or is re-exported,
and no public constructor takes the parts of a rational unchecked: the
`compile_fail` documentation tests of `Rational` check that `new_raw` does not
exist (`E0599`) and that a num-rational value does not convert into a
`Rational` (`E0277`). A third checks that rationals have no comparison
operators (`E0369`). The fields of `Congruence`, `IntegerDivision` and
`IntegerBezout` are private, and the `compile_fail` documentation test of
`Congruence` checks that a congruence cannot be built from its fields
(`E0451`). So are those of `PrimeField` and `PrimeResidue`, whose
`compile_fail` documentation tests check that a prime field and a residue
cannot be built from their fields (`E0451`) and that residues have no
comparison operators (`E0369`).

## Rules

### Types and invariants

- **Integer.** An integer of any size, with private contents. `bits()` is the
  bit length $\lvert x \rvert$ of the absolute value: 0 for zero, otherwise
  $\lfloor \log_2 \lvert x \rvert \rfloor + 1$. Integers are not checked
  against `max_integer_bits` when they are built from machine integers, since
  those have at most 64 bits; the operations of `Integer`, the integer kernel
  and the operations of `Rational` check them when they use them. `bits`
  does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states this count, 0 for zero and the bits of the absolute value for a
  negative integer, only in its documentation, and its result does not name
  it.
- **Congruence.** A modulus $m \gt 0$ and the least nonnegative residue
  $0 \le r \lt m$, established by `Congruence::new` and by `crt`, the only
  ways to build one. `Congruence::new` does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states the least nonnegative residue only in its documentation, and
  `residue()` does not name it.
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
the bit length, the operands as $x = a/b$ and $y = c/d$, $m = \lvert e \rvert$
for an exponent $e$, and
$W(x) = \max(1, \lceil \max(\lvert a \rvert, \lvert b \rvert) / 64 \rceil)$
for the machine words of $x$.

| Operation | Domain test | Bit bound | Charge |
| --- | --- | --- | --- |
| `new(n, d)` | $d = 0$ | $\max(\lvert n \rvert, \lvert d \rvert)$ | 1 |
| `parse_decimal` | syntax | $4 D$ | $D$ |
| `add`, `subtract` | none | $\max(\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert) + 1, \lvert b \rvert + \lvert d \rvert)$ | 1 |
| `compare` | none | only for the cross products: $\max(\lvert a \rvert + \lvert d \rvert, \lvert c \rvert + \lvert b \rvert)$ | 1 |
| `multiply` | none | $\max(\lvert a \rvert + \lvert c \rvert, \lvert b \rvert + \lvert d \rvert)$ | $W(x) W(y)$ |
| `divide` | $c = 0$ | $\max(\lvert a \rvert + \lvert d \rvert, \lvert b \rvert + \lvert c \rvert)$ | $W(x) W(y)$ |
| `negate` | none | $\max(\lvert a \rvert, \lvert b \rvert)$ | 1 |
| `inverse` | $a = 0$ | $\max(\lvert a \rvert, \lvert b \rvert)$ | 1 |
| `power(e)` | $m \le$ `max_exponent`, then $a = 0$ with $e \lt 0$ | $\max(P(a, m), P(b, m), \lvert a \rvert, \lvert b \rvert)$ | 1, one more for $m \ge 1$, and the words of each step of binary powering, as **Powers** below states |

- **Sums, products and quotients.** These are the bounds of the earlier
  implementation (FLD-R12). They bound the parts of the unreduced result, and
  reduction never lengthens a part. A bound above the limit is rejected even
  when the reduced result would fit: $1 + 1$ needs 3 bits.
- **Charges by machine words.** A product and a quotient of $x$ and $y$
  charge $W(x) W(y)$ units, the product of the machine words of their
  operands, as the products and the Euclidean divisions of
  [the integer kernel](#the-integer-kernel) do: one unit when both operands
  have at most 64 bits, and $2 \cdot 3 = 6$ units for $2^{100}/3$ and
  $5/2^{130}$, of 101 and 131 bits
  (`rational_products_quotients_and_powers_charge_word_products`). The
  amount depends only on the operands, never on the path that computes the
  result. A sum, a difference, a negation, an inverse, a comparison and
  `new` charge one unit whatever the size of their operands, and the
  reduction inside num-rational is not charged by its steps, so their work
  does not grow with the size of the numbers.
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
  4096 bits, is returned and $2^{4096}$ is rejected. The charge is made
  once, after the bound and before the power is computed, and counts the
  steps of binary powering by their machine words: one unit, one more for
  $m \ge 1$, and for each squaring of a power $y$ of the base $W(y)^2$
  units and for each multiplication of $y$ by $z$ $W(y) W(z)$ units, where
  the words of an operand $x^j$ are those of the larger of the bounds of
  its parts, $\min(P(a, j), j \lvert a \rvert)$ and
  $\min(P(b, j), j \lvert b \rvert)$ for $j \ge 1$ and 1 bit for $j = 0$: a
  part $a$ is below $2^{\lvert a \rvert}$, so $a^j$ has at most
  $j \lvert a \rvert$ bits, and the bound of $x^1$ is exact. Binary
  powering reads $m$ from its lowest bit and squares $\lvert m \rvert - 1$
  times and multiplies $w(m)$ times, where $\lvert m \rvert$ is the bit
  length of $m$ and $w(m)$ the number of its one bits. When every operand
  has at most 64 bits, so has its bound
  (`every_operand_of_one_word_charges_one_unit`), and the charge is
  $1 + \lvert m \rvert + w(m)$, the amount of release 0.1. It computes the
  numerator and the denominator separately, so a step costs at most twice
  what it is charged. For $(3/2^{64})^5$ the charge is
  $2 + 1 \cdot 2 + 2^2 + 3^2 + 2 \cdot 5 = 27$ units. A power whose steps
  need more work than is left fails before it is computed: with
  `max_exponent` raised to $2^{32}$ and `max_integer_bits` to $2^{33}$,
  $3^{4294967023}$ passes its bound and fails with `ResourceLimit` naming
  `max_work` under the default budget, with no work charged
  (`a_huge_power_is_refused_for_work_before_it_runs`). The parts of a
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

### The integer kernel

The arithmetic of `Integer` and the functions of the integer kernel run in
the order of the rationals: the domain test, where the operation has one;
the check of a bound against `max_integer_bits`, computed from the operands
alone; the charge, whose amount depends only on the operands; the
computation; the check of the bits of the integers that it computes; and
the check of the storage cost of the returned value with `check_storage` at
`LimitScope::Value`, so that it counts together with the open frames and
the reserved temporaries. A function of several steps checks its bound on
entry, before any charge; the one domain test that comes later, of a
negative power in `modular_power` whose base is not a unit, follows the
charges of the inverse. Euclid's steps in `gcd` and `lcm` are covered by
that bound, since their remainders decrease, and are only charged; every
other step, of the extended GCD, the quotient and the product of the LCM,
the modular inverse, binary powering and the merges of `crt`, checks its
own bound and charges before it computes, and checks the bits of the
integers that it computes. An integer that a function returns without
computing it, such as the power $a^0 \bmod m = 1$ for $m \gt 1$ or the
modulus of a congruence, is covered by the bound on entry. The intermediate
integers are checked by their bits only, never by their storage. The kernel
charges work and checks storage, and opens no frame and reserves no
temporary, so `Context::retained()` is the same before and after every call.
Write $W(x) = \max(1, \lceil \lvert x \rvert / 64 \rceil)$ for the
machine words of $x$: a product, a Euclidean division and a remainder of
$x$ and $y$ charge $W(x) W(y)$ units, and a sum, a difference, a negation
and an absolute value one unit.

| Operation | Domain test | Bit bound on entry | Charge | Result |
| --- | --- | --- | --- | --- |
| `a.add(b)`, `a.subtract(b)` | none | $\max(\lvert a \rvert, \lvert b \rvert) + 1$ | 1 | $a \pm b$ |
| `a.multiply(b)` | none | $\lvert a \rvert + \lvert b \rvert$ | $W(a) W(b)$ | $a b$ |
| `a.negate()`, `a.absolute()` | none | $\lvert a \rvert$ | 1 | $-a$, $\lvert a \rvert$ |
| `a.divide_with_remainder(b)` | $b = 0$ | $\max(\lvert a \rvert, \lvert b \rvert)$ | $W(a) W(b)$ | $(q, r)$, $a = q b + r$, $0 \le r \lt \lvert b \rvert$ |
| `a.exact_quotient(b)` | $b = 0$ | $\max(\lvert a \rvert, \lvert b \rvert)$ | $W(a) W(b)$ | `Quotient(q)` when $b \mid a$, else `NotDivisible` |
| `gcd(a, b)` | none | $\max(\lvert a \rvert, \lvert b \rvert)$ | each Euclid step $(x, y) \mapsto (y, x \bmod y)$: $W(x) W(y)$ | $g \ge 0$, $\gcd(0, 0) = 0$ |
| `lcm(a, b)` | none | $\max(\lvert a \rvert, \lvert b \rvert)$, and before the product $\lvert a / g \rvert + \lvert b \rvert$ | the steps of `gcd`, one exact quotient and one product | $\lvert a b \rvert / g \ge 0$, 0 when an operand is 0 |
| `extended_gcd(a, b)` | none | $\max(\lvert a \rvert, \lvert b \rvert) + 2$ | each round: one Euclidean division, two products and two differences | $(g, s, t)$, $g = s a + t b$, $g \ge 0$ |
| `modular_inverse(a, m)` | $m \le 0$ | $\max(\lvert a \rvert, \lvert m \rvert)$, and for $m \gt 1$ also $\lvert m \rvert + 2$ | the remainder $a \bmod m$; for $m \gt 1$ the rounds of `extended_gcd` on it and $m$, and for a unit the remainder of $s$ modulo $m$ | `Inverse(v)`, $0 \le v \lt m$, or `NonUnit(g)` |
| `modular_power(a, e, m)` | $m \le 0$; after the inverse, $e \lt 0$ with a base that is not a unit | $\max(\lvert a \rvert, \lvert e \rvert, \lvert m \rvert)$, and for $e \ne 0$ also $2 \lvert m \rvert$ | the remainder $a \bmod m$ or the inverse; then each multiplication and each squaring: one product and one remainder modulo $m$ | $a^e \bmod m$ in $[0, m)$ |
| `Congruence::new(r, m)` | $m \le 0$ | $\max(\lvert r \rvert, \lvert m \rvert)$ | the remainder: $W(r) W(m)$ | $r \bmod m$ in $[0, m)$ |
| `crt(congruences)` | none: the moduli are positive | every residue and modulus, and at least 1 | each merge, as below | `Solution(r mod l)` or `Inconsistent` |

- **Order.** A zero divisor and a modulus that is not positive are reported
  before any check of `max_integer_bits` and before any charge, so the
  error is the same under every limit and charges nothing. The earlier
  implementation charged and checked its operands first and tested the
  divisor and the modulus after, as its coefficient-field contract stated;
  this order is a change of behaviour on purpose.
- **Euclidean division.** The remainder is never negative:
  $q = \mathrm{sign}(b) \lfloor a / \lvert b \rvert \rfloor$, rounded down
  for $b \gt 0$ and up for $b \lt 0$, so $-7$ divided by $2$ is
  $(-4, 1)$ and by $-2$ is $(4, 1)$. `exact_quotient` takes the same
  division and returns `NotDivisible`, a value and not an error, when the
  remainder is not zero. `divide_with_remainder` does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states the Euclidean remainder only in its documentation, and its
  result does not name it.
- **GCD and Bézout coefficients.** The bound of `gcd` covers every step,
  since the remainders decrease. `extended_gcd` runs on $\lvert a \rvert$
  and $\lvert b \rvert$ and gives the signs of $a$ and $b$ to $s$ and $t$:
  $(240, 46)$ gives $(2, -9, 47)$ and $(0, 0)$ gives $(0, 0, 0)$. The
  coefficients of the rounds alternate in sign and never exceed
  $\max(\lvert a \rvert, \lvert b \rvert)$ in absolute value, so the bound
  of $\max(\lvert a \rvert, \lvert b \rvert) + 2$ bits covers every product
  and difference of a round. `extended_gcd` does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states these coefficients only in its documentation, and its result
  does not name the choice. `gcd` and `lcm` do not follow it either: they
  state that their results are nonnegative, with $\gcd(0, 0) = 0$ and an LCM
  of 0 when an operand is 0, only in their documentation, and their results
  do not name it.
- **Modular inverse.** Modulo 1 every residue is the unit 0, with inverse
  0. For $m \gt 1$ the result is `Inverse(v)` when
  $g = \gcd(a \bmod m, m) = 1$, and otherwise `NonUnit(g)`, which is $m$ for
  a residue of zero; a missing inverse is a value, not an error. The bound
  $\lvert m \rvert + 2$ is checked whether the residue is zero or not, since
  only the operands decide it before the charge. These are functions on
  integers, not the operations of a residue ring. `modular_inverse` does not
  follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states the representative $0 \le v \lt m$ of the inverse only in its
  documentation, and its result does not name it.
- **Modular power.** For $e \lt 0$ the base is first inverted, and a base
  that is not a unit, a residue of zero included, fails with
  `Fault(OutsideDomain)` after the charges of the inverse. Every product
  of two residues is the integer product followed by its remainder modulo
  $m$, on one path under every limit, so the charges depend only on the
  operands; the bound $2 \lvert m \rvert$ covers each product and, for
  $m \gt 1$, the bound $\lvert m \rvert + 2$ of the inverse. A power whose
  product bound exceeds `max_integer_bits` fails with `ResourceLimit` naming
  `max_integer_bits` before any charge: under the default limits a power
  with a nonzero exponent modulo a modulus of more than 2048 bits fails.
  The earlier implementation switched to doubling and addition when the
  bits of the two factors added up to more than `max_integer_bits`, so its
  charges changed with the limits;
  `a_modular_power_takes_one_path_under_every_bit_limit` rejects that
  deviation: $250^{231} \bmod 251$ is 250 with the same work under the
  default limits and under 16 bits, and fails under 15 and 8 bits with the
  amount 16 and no work. The exponent is checked by its bits against
  `max_integer_bits` only, never against `max_exponent`: the result is a
  residue, which does not grow with the exponent. `modular_power` does not
  follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states that its result is the residue in $[0, m)$, and that $a^0 = 1$
  with $0^0$ included, only in its documentation, and its result names
  neither.
- **Chinese remaindering.** The moduli need not be coprime. The congruences
  are merged in order into $r \bmod M$ from $0 \bmod 1$, the empty system's
  solution. Merging $x \equiv r_i \pmod{m_i}$ runs the extended GCD
  $g = s M + t m_i$, the difference $\delta = r_i - r$, the Euclidean
  division of $\delta$ by $g$, the exact quotient $n = m_i / g$, the
  remainders of $\delta / g$ and of $s$ modulo $n$, their product modulo $n$,
  $k$, and the products $M n$ and $M k$ and the sum $r + M k$, each with its
  own bound and charge. The first congruence whose $\delta$ is not divisible
  by $g$ ends the computation with `Inconsistent`, a value and not an error;
  otherwise the result is the solution modulo the LCM of the moduli. The
  check on entry reads every congruence once, before any charge, so a
  congruence built under other limits is checked against the receiving
  `max_integer_bits`. Its bound is at least one bit, the bits of the
  modulus 1 of the empty system's solution, so that under
  `max_integer_bits` 0 the empty system fails with the amount 1, as
  `Congruence::new` does for $0 \bmod 1$. `crt` does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states only in its documentation that the solution has the least
  nonnegative residue of a congruence, and its result does not name it.
- **Storage.** Only the returned value is admitted, by the formulas of
  [storage](#storage); the storage of the operands is not checked. The
  earlier implementation also checked the nodes and bytes of the operands,
  so that $\gcd(-12, 18)$ returned no value under one node or 17 bytes; in
  kalyx it returns 6 under one node and 7 bytes, the cost of 6
  (`integer_results_are_measured_by_their_bits`).

### Division by zero

`divide` by zero, `inverse` of zero, `new` with a zero denominator and a zero
base with a negative exponent fail with `Fault(DivisionByZero)`, and so do
`divide_with_remainder` and `exact_quotient` of `Integer` by zero. The zero
test comes before any check of `max_integer_bits` and before any charge, so
the error is the same under every limit and every remaining work, and nothing
is charged; only the exponent check of a power comes first. A modulus that is
not positive, which the integer kernel reports as `Fault(OutsideDomain)`, is
tested at the same place.

### Storage

`StorageCost` for a rational $n/d$ is one node and
$\lvert n \rvert + \lvert d \rvert + 3$ bytes, the formula of the
[context](../context/contract.md#storage-costs), saturating at `u64::MAX`.
Zero costs $(1, 4)$. The `measure` of `Rationals` is the same formula; it
takes constant time, since the bit lengths are read from the stored
integers.

The results of the integer kernel follow the
[storage formulas](../../architecture.md#storage-bytes) of the architecture:
an integer $z$ costs $(1, \lvert z \rvert + 4)$, the cost of the rational
$z/1$; a result of several integers, `IntegerDivision`, `IntegerBezout` and
`Congruence`, the sum of their costs, so $(2, \lvert q \rvert + \lvert r \rvert + 8)$,
$(3, \lvert g \rvert + \lvert s \rvert + \lvert t \rvert + 12)$ and
$(2, \lvert r \rvert + \lvert m \rvert + 8)$; an outcome the cost of the
integer that it carries, and $(1, 4)$ for `NotDivisible` and `Inconsistent`.
Each returned value is admitted with `check_storage` at `LimitScope::Value`
against `max_nodes` and `max_storage_bytes`, the totals that the context
retains. The earlier implementation compared the bytes of the operands and
of each composite result with a separate bound on one value,
`max_symbolic_bytes`; in kalyx that bound is the special case of the total
in which nothing else is retained.

### Display, order and equality

- **Display.** An integer is its decimal digits with a leading `-` when
  negative. A rational is its numerator, followed by `/` and its denominator
  unless the denominator is 1: `-3/4`, `5`, `0`. A congruence is
  `r mod m`, an outcome of `crt` its congruence or `inconsistent`, and the
  result of `extended_gcd` `gcd: g; left: s; right: t`. The text is
  deterministic and depends only on the value. As
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

### Prime fields

`PrimeField` is the parent of the prime field $\mathbb F_p$ of a prime
$p \lt 2^{32}$. It holds the modulus in a private field, which `modulus()`
reads, and its derived `PartialEq`, `Eq` and `Hash` compare the moduli.
Its `Element` is `PrimeResidue`, the least nonnegative residue
$0 \le r \lt p$ of the class in a machine word, which `value()` reads; a
residue does not repeat its field, has no equality and is built only by the
methods of its field. The `Undecided` of `PrimeField` is
`std::convert::Infallible`. `Debug` shows the stored modulus and the stored
residue.

- **Construction.** `PrimeField::new(p, context)` is the only way to build
  a prime field. A modulus below 2, and an even modulus other than 2, fails
  with `Fault(OutsideDomain)` before any check of `max_integer_bits` or any
  charge, and before any `Integer` is built; the modulus 2 is accepted at
  once, without a check or a charge. An odd modulus $p \ge 3$ is decided by the
  strong probable-prime test (Miller–Rabin) to the bases 2, 7 and 61. With
  $p - 1 = d \cdot 2^s$ and $d$ odd, a base $a$ is passed when
  $x = a^d \bmod p$ is 1 or $p - 1$, or when one of at most $s - 1$
  squarings of $x$ modulo $p$ gives $p - 1$; a base equal to $p$, as 7 is
  for $\mathbb F_7$ and 61 for $\mathbb F_{61}$, is skipped, since its
  residue 0 never passes. A
  prime passes every base, and no composite below 4,759,123,141 passes all
  three (G. Jaeschke, *On strong pseudoprimes to several bases*, Math.
  Comp. 61 (1993), 915–926), so the test is exact for every `u32`. Each
  power $a^d \bmod p$ and each squaring is one call of `modular_power` of
  [the integer kernel](#the-integer-kernel), with its checks and charges:
  the bound $\max(\lvert a \rvert, \lvert d \rvert, 2 \lvert p \rvert)$
  of a power is $\max(6, 2 \lvert p \rvert)$, since the base 61 has 6 bits
  and $\lvert d \rvert \lt \lvert p \rvert$, so $2 \lvert p \rvert$ for
  $p \ge 5$, and the bound of a squaring is $2 \lvert p \rvert$; under
  the default limits every `u32` passes them. The test takes the same path
  for $p$ under every limit, so its work depends only on $p$. A composite
  modulus fails with `Fault(OutsideDomain)` after the charges of the test,
  which are kept; no field is built from it and the context retains
  nothing more. A failed check or charge of the test reports the limit or
  the request failure of `modular_power`. The test is part of the
  constructor and is not a public entry.
- **Element operations.** Every method that takes residues first tests
  that each is below $p$: a residue at or above $p$ can belong only to
  another field, and fails with `Fault(OutsideDomain)` before any check or
  charge; a residue of another field below $p$ is taken as a residue of
  the receiver, as the receiver rule of
  [the coefficient-field trait](#the-coefficient-field-trait) assumes
  (`a_residue_beyond_the_modulus_is_outside_the_domain`).
  `inverse` and `divide` then test their element or divisor for zero.
  Every method that builds a residue then checks a bound on its bits
  against `max_integer_bits`, then charges, and only then computes it with
  a kernel. The bound of a new residue is $\lvert p \rvert$, the bit length
  of the modulus, whatever the residue, zero included.

| Method | Domain tests | Bit bound | Charge | Result |
| --- | --- | --- | --- | --- |
| `zero`, `one` | none | $\lvert p \rvert$ | 1 | 0, 1 |
| `from_integer(n)` | none | $\max(\lvert n \rvert, \lvert p \rvert)$ | 1, then $W(n) W(p)$ for the Euclidean division of $n$ by $p$ | $n \bmod p$ |
| `negate(a)` | $a \ge p$ | $\lvert p \rvert$ | 1 | `sub(0, a)` $= (p - a) \bmod p$ |
| `add(a, b)`, `subtract(a, b)`, `multiply(a, b)` | $a \ge p$, $b \ge p$ | $\lvert p \rvert$ | 1 | `add(a, b)`, `sub(a, b)`, `mul(a, b)` |
| `inverse(a)` | $a \ge p$, then $a = 0$ | $\lvert p \rvert$ | 32 | `inverse(a)` $= a^{p - 2} \bmod p$ |
| `divide(a, b)` | $a \ge p$, $b \ge p$, then $b = 0$ | $\lvert p \rvert$ | 32 | `mul(a, inverse(b))` |
| `zero_test(a)` | $a \ge p$ | none | none | `Zero` exactly for the residue 0 |
| `same_parent(other)` | none | none | none | whether the moduli are equal |
| `measure(a)` | none | none | none, and no context | $(1, \lvert r \rvert + 4)$ for the residue $r$ |

- **The kernels.** The results are computed by four private kernels of
  `PrimeField`: `fn add(self, a: u32, b: u32) -> u32`, `sub` and `mul` of
  the same signature, which reduce a sum $a + b$, a difference
  $a + p - b$ and a product $a b$ modulo $p$ in 64-bit intermediates, and
  `fn inverse(self, a: u32) -> u32`, which raises $a$ to the power $p - 2$
  by binary powering over the bits of $p - 2$ from the lowest, at most 32
  rounds, the inverse of a nonzero $a$ by Fermat's little theorem. They
  take no context, charge nothing and cannot fail on the residues of their
  field: the constructor makes $p$ at least 2, so no remainder is taken
  modulo zero and $p - 2$ does not go below zero; the residues are below
  $p$, which the methods test, so $a + p - b$ does not go below zero; and
  $(p - 1)^2 \lt 2^{64}$, so no product overflows. The charge of 32 units
  of `inverse` and `divide` is the number of rounds for the largest $p$,
  made once before the kernel whatever $p$ is.
- **The image of an integer.** `from_integer` checks
  $\max(\lvert n \rvert, \lvert p \rvert)$, the bound of the Euclidean
  division by $p$, before its own charge, then divides with
  `Integer::divide_with_remainder` of the integer kernel, which checks the
  same bound and passes it, charges the division and admits its result
  with `check_storage` at `LimitScope::Value`, and reads the remainder.
- **Zero.** The inverse of zero and every quotient by zero fail with
  `Fault(DivisionByZero)` before any check and any charge, so under every
  limit, with no work left and when the request is cancelled, and nothing
  is charged (`a_prime_field_inverts_zero_to_division_by_zero_without_a_charge`).
- **Zero tests and parents.** `zero_test` reads the residue and always
  decides; `same_parent` compares the moduli. Both take constant time,
  allocate nothing and charge nothing
  (`prime_fields_decide_every_zero_test_without_a_charge`).
- **Storage.** `measure` is one node and $\lvert r \rvert + 4$ bytes for
  the residue $r$, the cost $(1, \lvert r \rvert + 4)$ of the integer $r$
  in the [storage formulas](../../architecture.md#storage-bytes) of the
  architecture; the modulus belongs to the parent and is not counted. Zero
  costs $(1, 4)$, and the residue $p - 1$ of
  $\mathbb F_{4294967291}$ costs $(1, 36)$
  (`prime_fields_measure_their_elements_by_the_storage_formula`). It takes
  constant time.
- **No frames or temporaries.** The methods open no frame and reserve no
  temporary, so `Context::retained()` is the same before and after every
  call; apart from `from_integer`, whose integer division admits its result
  against the storage limits, they succeed under `max_frames` and
  `max_storage_bytes` of 0 (`prime_fields_hold_no_frame_or_reservation`).
- **Representatives.** `PrimeResidue::value` does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states that the residue is the least nonnegative one, $0 \le r \lt p$,
  so that $-1$ is $p - 1$, only in its documentation, and its result does
  not name it.
- **Bits.** The checks of `max_integer_bits` of `PrimeField::new` and of
  the methods that build a residue do not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions),
  as [CTX-R07](../context/contract.md#ctx-r07) states for every check of
  `max_integer_bits`: each compares a bound of its own, computed from the
  modulus before the result, $\max(6, 2 \lvert p \rvert)$ for a power of
  the test of an odd $p \ge 3$ and $2 \lvert p \rvert$ for a squaring,
  $\lvert p \rvert$ for a new residue, and
  $\max(\lvert n \rvert, \lvert p \rvert)$ for `from_integer`, which only
  their documentation states, and the amount of the error does not name the
  bound.
- **Deviations of the earlier implementation.** Its prime field was built
  from a modulus whose size alone it checked, contrary to its rule that a
  parent is built only from validated defining data: its caller decided
  primality by trial division, at one unit for each divisor up to
  $\sqrt{p}$, and its inverse would go below zero for $p \lt 2$. The
  constructor now decides primality itself and rejects every modulus that
  is not prime, and `a_prime_field_rejects_the_modulus_zero`,
  `a_prime_field_rejects_the_modulus_one`,
  `a_prime_field_rejects_the_modulus_four` and
  `a_prime_field_rejects_the_strong_pseudoprime_3215031751` reject that
  deviation: $3215031751 = 151 \cdot 751 \cdot 28351$ is a strong
  pseudoprime to the bases 2, 3, 5 and 7, and of the bases of the test only
  61 reveals it.
  `a_prime_field_accepts_the_primes_2_3_and_4294967291` builds the fields
  of 2, 3, 7, 61, 65537 and 4294967291 under the default limits, and runs
  the constructor on 4294967291 and on 3215031751 under the work and
  cancellation checks of the property-testing tool. The earlier
  implementation failed the inverse of zero with an invariant error of its
  factorization, and charged its inverse one unit for each bit of $p - 2$
  inside its loop; the inverse of zero now fails with `DivisionByZero`, as
  every field's does, and the inverse is charged once, before its kernel
  (`inverses_charge_a_fixed_amount_and_nothing_for_zero`).

## Requirements

The requirement identifiers are those of the coefficient fields of the
earlier implementation of the casξ computer algebra system; they are never
renumbered or reused. Each entry states the part of the requirement that
applies to the rationals, the prime fields and the trait, as kalyx
implements it, and the tests that are its evidence. Tests are in `tests/numbers.rs`, and those of
FLD-R14 and FLD-R15 in `tests/integers.rs`, unless the entry names
`tests/coefficient.rs` or a file below `src/number/`. The bit check of
an integer is [CTX-R07](../context/contract.md#ctx-r07) of the context.

### FLD-R01

**Canonical forms.** A rational is a reduced fraction of an integer numerator
and a positive denominator, zero being $0/1$. Two canonical forms are equal
exactly when they denote the same number, and every rational has one; every
operation returns one.

In a prime field every element is the least nonnegative residue of its
class, which every method returns.

- **Implemented here.** The private fields of `Rational`, the reduction of
  `new` and of the kernels, and the fast paths, which build a fraction without
  a reduction only where it is canonical by construction; the private field
  of `PrimeResidue` and the kernels of `PrimeField`, which reduce every
  result modulo $p$.
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
  `other_operands_use_the_general_path`. For the prime fields,
  `prime_fields_have_unique_canonical_forms` and
  `prime_fields_agree_with_the_small_model` in `tests/coefficient.rs`, and
  `every_residue_triple_below_32_and_every_inverse_modulo_65521_is_exact`
  in `src/coefficient/prime/tests.rs`, which checks the kernels directly.

### FLD-R02

**Division and inverse.** A zero divisor, or a zero element to invert, is the
domain error `DivisionByZero`; otherwise the result is the quotient or the
inverse, whose product with the element is 1. kalyx strengthens the priority:
the zero test comes before every size check and every charge, so a zero
divisor is `DivisionByZero` in every state of the context and charges
nothing.

The earlier requirement made the prime fields an exception, whose inverse of
zero was an invariant failure; in kalyx it is `DivisionByZero` there too, as
[prime fields](#prime-fields) states.

- **Implemented here.** `Rational::new`, `divide`, `inverse` and `power`, and
  `inverse` and `divide` of `Rationals` and of `PrimeField`.
- **Evidence.** Positive: `rationals_have_inverses_and_zero_has_none` and
  `prime_fields_have_inverses_and_zero_has_none` in `tests/coefficient.rs`.
  Negative: `division_by_zero_fails_before_any_charge`, with no work left and
  a bit limit of 0, and
  `a_prime_field_inverts_zero_to_division_by_zero_without_a_charge`, under a
  bit limit of 1 and a cancellation. Also
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
succeeds. `Rational::power` does not follow
[convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
it states $0^0 = 1$ only in its documentation, and its result does not name
it.

- **Implemented here.** `Rational::power`, with `power_bits`,
  `power_charge` and `power_part` of `src/number/power.rs`.
- **Evidence.** Positive: `ex3_integer_powers_use_the_empty_product`.
  Negative: `the_power_checks_the_exponent_then_the_zero_base_then_the_bits`.
  Also `a_power_beyond_max_integer_bits_is_rejected_before_any_charge`,
  `a_huge_power_is_refused_for_work_before_it_runs`,
  `power_bound_is_exact_for_powers_of_two_at_the_default_bit_limit`,
  `computational_growth_is_bounded`, `ex5_growth_is_checked_before_arithmetic`,
  and in `src/number/power.rs` `the_power_bound_is_exact_within_one_bit`,
  `the_power_bound_is_exact_for_powers_of_two_and_holds_for_wide_bases`,
  `the_power_bound_holds_its_claims_for_large_exponents`,
  `the_power_bound_holds_where_the_last_unit_of_the_logarithm_decides`,
  `the_power_bound_can_be_two_bits_above_just_below_2_pow_32`,
  `binary_powering_matches_repeated_products`,
  `the_charge_of_a_power_counts_the_words_of_its_steps` and
  `every_operand_of_one_word_charges_one_unit`.

### FLD-R04

**Zero tests.** A zero test answers zero, nonzero or undecided; the zero tests
of the rationals and of the prime fields are exact and never undecided, which
their reason type `Infallible` makes impossible.

- **Implemented here.** `zero_test` of `Rationals` and of `PrimeField`.
- **Evidence.** Positive: `rationals_decide_every_zero_test_without_a_charge`
  and `prime_fields_decide_every_zero_test_without_a_charge` in
  `tests/coefficient.rs`. Negative: `rationals_have_inverses_and_zero_has_none`
  and `prime_fields_have_inverses_and_zero_has_none` in
  `tests/coefficient.rs`, which check that the test answers zero exactly for
  the zero of the model.

### FLD-R12

**Accounting under the request context.** The effect of every operation on
the context is a sequence of charges that stops at the first failure; the
amounts depend only on the operands. The bit bounds of the rationals are the
closed forms of [checks and charges](#checks-and-charges); a bound above
`max_integer_bits` fails with `ResourceLimit` naming `max_integer_bits`, and
in kalyx it does so before the charge, so the work is unchanged. Under limits
at or above the bound, with work left and without a deadline or
cancellation, the value is returned.

The element operations of the prime fields check the bounds of
[prime fields](#prime-fields) before their charges, which depend only on the
modulus and, for `from_integer`, on the integer.

- **Implemented here.** Every operation of `Rational`, of `Rationals` and of
  `PrimeField`.
- **Evidence.** Positive: `operations_charge_one_unit_and_powers_by_their_exponent`
  and `rational_products_quotients_and_powers_charge_word_products`.
  Negative: `an_addition_beyond_max_integer_bits_is_rejected_before_any_charge`,
  `a_multiplication_beyond_max_integer_bits_is_rejected_before_any_charge`
  and `a_power_beyond_max_integer_bits_is_rejected_before_any_charge`. Also
  `a_huge_power_is_refused_for_work_before_it_runs`,
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
  in `tests/command.rs`, `rationals_check_and_charge_new_elements`,
  `rationals_measure_their_elements_by_the_storage_formula`,
  `prime_fields_check_and_charge_new_elements`, with one bit and one unit
  below every amount, `prime_fields_are_charged_exactly_and_roll_back`,
  `prime_fields_are_cancelled_at_every_charge_point` and
  `prime_fields_measure_their_elements_by_the_storage_formula` in
  `tests/coefficient.rs`, and in `src/number/positive_compare_tests.rs`
  `the_comparison_takes_the_first_path_that_applies`,
  `positive_comparison_matches_an_independent_small_integer_oracle`,
  `equal_adjacent_and_disjoint_product_bit_ranges_remain_exact`,
  `hundred_thousand_bit_widths_check_only_the_bound_of_the_cross_products` and
  `positive_comparison_preserves_every_small_bit_work_boundary_and_priority`.

### FLD-R14

**Integers.** The part that applies to the arithmetic of `Integer` and to
the integer kernel: integers of any size, each its own canonical form; sums,
differences, products and negation; exact division, which is
`DivisionByZero` for a zero divisor, $0 / 0$ included, returns the quotient
when the divisor divides and is otherwise `NotDivisible`, a value and not an
error; a GCD that is nonnegative, divides both operands and is divisible by
every common divisor, with $\gcd(0, 0) = 0$; and an LCM of
$\lvert a b \rvert / \gcd(a, b)$, and 0 when an operand is 0. Under limits at
or above the stated bounds, when the charges succeed, an operation returns
its outcome. kalyx differs from the earlier requirement on purpose in three
places, as [the integer kernel](#the-integer-kernel) states: the zero divisor
is tested before any check and charge; an integer costs
$(1, \lvert z \rvert + 4)$ in place of one node and
$\lceil \lvert z \rvert / 8 \rceil + 8$ bytes, and only the returned value
is admitted; and the bounds are those of the table there, none above the
estimates of the earlier requirement: a sum needs
$\max(\lvert a \rvert, \lvert b \rvert) + 1$ bits, where the earlier
estimate was one bit more.
The integer coefficient ring, its exact division with the result state
inexact and the maps out of $\mathbb{Z}$ are not part of this component.

- **Implemented here.** The operations of `Integer`, `gcd`, `lcm` and
  `extended_gcd` in `src/number/integer.rs`.
- **Evidence.** Positive: `ex1_gcd_lcm_and_bezout_coefficients` and
  `the_stated_bounds_of_the_integer_witnesses_admit_their_results`, which
  runs the witnesses of the GCD, the LCM, the ring operations, the negation
  and exact division of the earlier specification at their stated bounds,
  recomputed by the storage formulas of kalyx. Negative:
  `integer_operations_check_bits_before_charging`, with one bit below every
  bound and a zero divisor under no bits and no work. Also
  `bezout_identity_holds_for_seeded_operands`,
  `lcm_times_gcd_is_the_absolute_product`,
  `integer_results_are_measured_by_their_bits`,
  `representative_operations_succeed_at_exact_limits_and_fail_one_below`,
  `cancellation_at_every_charge_point_of_the_representative_operations`,
  `seeded_random_calls_of_the_representative_operations_do_not_panic` and, in
  `src/number/integer_tests.rs`, `bezout_and_lcm_all_signs_and_zeros` and
  `gcd_lcm_and_bezout_hold_for_seeded_150_bit_operands`.

### FLD-R15

**Residues of the integers.** The part that applies to the functions
`modular_inverse`, `modular_power` and `Congruence::new`, which are
functions on integers and not the operations of a residue ring: a modulus
$m \le 0$ is `OutsideDomain`; residues are the least nonnegative ones,
$0 \le r \lt m$; modulo 1 every residue is the unit 0, with inverse 0; a
unit has its inverse, and a non-unit gives `NonUnit(g)` with
$g = \gcd(a \bmod m, m)$, which is $m$ for a residue of zero; $a^0 = 1$,
$0^0$ included; a negative power of a non-unit is `OutsideDomain`; a
product of residues is the integer product followed by its remainder, on
one path, bounded by twice the bits of the modulus; and the exponent is
checked by its bits against `max_integer_bits`, never against
`max_exponent`. The charges do not depend on the limits. Under limits at or
above the bounds of [the integer kernel](#the-integer-kernel), among them
$\lvert m \rvert + 2$ bits for an inverse modulo $m \gt 1$ and
$2 \lvert m \rvert$ for a power with a nonzero exponent, and at or above the
storage of the outcome, when the charges succeed, a function returns its
outcome. kalyx differs from the earlier requirement on purpose in four
places, as the items on the order, the modular inverse and the storage of
[the integer kernel](#the-integer-kernel) and the section
[storage](#storage) state: the modulus is tested before any check and
charge, where the earlier requirement charged and revalidated the residues
and the modulus first; an integer costs $(1, \lvert z \rvert + 4)$ in place
of one node and $\lceil \lvert z \rvert / 8 \rceil + 8$ bytes, the inverse
checks the bits of its estimate but not its six nodes and
$6 (\lceil b / 8 \rceil + 8)$ bytes, and only the returned value is
admitted; a non-unit gives `NonUnit(g)`, where the earlier counterpart
`modular_inverse` returned no inverse; and the bound $\lvert m \rvert + 2$
of an inverse is checked for a residue of zero as well, where the earlier
requirement states no estimate for zero, so that the inverse of zero modulo
$m \gt 1$ needs two bits more than the modulus has. That is the one bound
above the estimates of the earlier requirement; the others are its
estimates of $b + 2$ bits for an inverse and $2 b$ bits for each product of
a power, $b$ being the bits of the modulus. The parents of residue rings,
their zero rules and the mismatch of moduli are not part of this component.

- **Implemented here.** `modular_inverse`, `modular_power`,
  `Congruence::new` and `crt` in `src/number/integer.rs`.
- **Evidence.** Positive: `ex2_modular_powers_and_inverses`,
  `ex3_chinese_remaindering_accepts_non_coprime_moduli` and
  `the_stated_bounds_of_the_integer_witnesses_admit_their_results`, which
  runs the witnesses of the inverse, the non-units, the modulus one, the
  powers and the reduction of a residue at their stated bounds. Negative:
  `a_modular_power_takes_one_path_under_every_bit_limit` and
  `non_positive_moduli_and_negative_powers_of_non_units_are_outside_the_domain`.
  Also `modular_operations_match_exhaustive_residues`,
  `crt_general_moduli_empty_duplicates_and_inconsistency`,
  `crt_solutions_satisfy_every_congruence_and_are_unique_modulo_the_lcm`,
  `request_budget_receiving_limits_preflight_and_cancellation`, the three
  tests of the representative operations named under FLD-R14 and, in
  `src/number/integer_tests.rs`,
  `modular_powers_and_inverses_match_repeated_multiplication` and
  `crt_systems_of_up_to_four_congruences_match_brute_force`.

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
3. **Field properties.** `tests/coefficient.rs` runs the property-testing
   tool of `tests/field_properties/` on `Rationals`. The checks of the tool
   are generic over its ring layer and its field layer, which the parents of
   the library enter through one wrapper whose operations are those of
   `CoefficientRing` and `CoefficientField`; the ring axioms and the field
   axioms are separate checks, and a ring runs only the former. The tool
   checks the axioms, agreement with a model of $\mathbb{Q}$ as reduced
   `i128` fractions with their own GCD on small operands, unique stored
   forms, the zero test, the errors of zero divisors, characteristic zero,
   the map from the integers, the laws of the polynomials over
   $\mathbb{Q}$ and their agreement with that model coefficient by
   coefficient, and, on fixed inputs, the work accounting and the
   cancellation of the operations of both layers and of the arithmetic of
   the polynomials: zero, one, the generator, constants, sums, differences,
   products, powers, derivatives and negation. Five families state
   associativity, commutativity and distributivity on the ring layer, and
   inverses and canonical uniqueness on the field layer: each runs 1,000
   cases from a fixed seed of the SplitMix64 sequence of
   `tests/support/mod.rs`, compared with the model on operands of at most
   16 bits so that the model never overflows, and 50 cases with operands of
   about 256 bits, checked by identities alone. The generator samples zero,
   small and larger integers, power-of-two denominators and general
   fractions. The ring axioms fail on a parent of the tests that is not
   commutative, the rational quaternions, at the commutativity of the
   product (`the_tool_rejects_a_noncommutative_parent`). The same checks
   run on `PrimeField` of each of the primes 2, 3, 7, 65537 and 4294967291,
   with a model of $\mathbb F_p$ as `u64` residues with `u128` sums and
   products and an inverse by the extended Euclidean algorithm, and with
   characteristic $p$ in place of characteristic zero: the image $n \cdot 1$
   is zero exactly when $p$ divides $n$, $p \cdot 1 = 0$,
   $-1 \cdot 1 = (p - 1) \cdot 1$, and $(a + b)^p = a^p + b^p$ with powers
   by binary powering through the product of the field. The axioms take
   every residue and every triple for $p \le 7$; the five families keep
   their seeds and case counts, with small residues, and residues in
   $[p - 50, p)$ as large operands; the polynomials over $\mathbb F_p$ have
   residue coefficients, and every pair of the polynomials of degree at most
   3 over $\mathbb F_2$ and at most 2 over $\mathbb F_3$ is checked
   (`every_small_polynomial_pair_satisfies_the_laws`). A residue has no
   public constructor, so the adapter of a prime field builds its inputs
   through `from_integer`, which the checks of the integer images compare
   with the model on their own.
4. **No message text.** No test asserts the message of an error; tests
   compare the kind, the span and the exceeded limit.
5. **Work.** Tests assert the amounts that this contract fixes, and that a
   rejected operation charges nothing; they assert no other amount.
6. **Integer kernel.** `tests/integers.rs` checks every operation of
   `Integer` at its bound and one bit below, with one-word and multi-word
   operands and the amounts of the table; the Bézout identity, the product
   of the LCM and the GCD and the solutions of systems of congruences on
   1,000 cases each, from fixed seeds of a SplitMix64 generator written in
   the test, against models in `i128`; the domain errors, the storage of
   every kind of result at its exact cost and one byte and one node below;
   the witnesses of the integers and residues of the earlier
   specification at their stated bounds, with the bytes recomputed by the
   formulas of kalyx; and its representative operations, the product of
   large integers, the Euclidean division, the modular power and Chinese
   remaindering, on seven inputs: each returns its outcome with exactly the
   work, the nodes, the bytes and the bits that it needs and fails with one
   less, with the limit named; a cancellation at each of its charge points
   gives `Cancelled`; and 4,000 calls from fixed seeds, 1,000 for each
   operation, end with a value or an admissible error and never panic. Each
   of these leaves its inputs and `Context::retained()` unchanged. The
   kernel does not recurse, so it has no case of depth.

## Extractability

The trait is shaped for extraction as the architecture requires: associated
types and `&self` methods, no default methods, no lifetime parameters on the
parents and no closures. The rationals are not written in the provable
subset: they allocate through num-bigint and num-rational, whose operations
are outside the subset and would be trusted external functions, and the
literal scanner iterates over characters. The kernels of
`src/number/arithmetic.rs` and `src/number/power.rs` use `match` instead of
combinators with closures and instead of `if let`, and have at most one loop
each; `log2_upper` in `src/number/power.rs` is a `const fn` over machine
integers. No proof target is registered for this component.

The integer kernel in `src/number/integer.rs` is written to follow the
provable subset of the krepi convention, its constructs R1 to R7, its loop
shapes and its design rules 3 to 9, apart from its integers, whose
num-bigint operations would be trusted external functions; it has not been
extracted. No function item is passed as a value, no iterator adapter or
combinator with a closure is used, and dispatch is a `match` or an `if`.
Each function has at most one loop, at the top level of its body: Euclid's
algorithm, the extended Euclidean algorithm, binary powering, the scan of
the congruences and their merge are each the only loop of a helper that
holds the owned integers across its loop and has no `?` and no `return`
before it, and the checks that return early are in the loopless functions
that call the helpers; slices are walked by index loops, and no loop
condition is a macro. Design rules 1 and 2 are met as adapted, not as
stated:

- **Rule 1, check, then execute.** As in the rule "Check, then write" of
  the [context](../context/contract.md#frames-and-temporaries), the charges
  count among the checks: the domain test of the divisor or the modulus and
  the bound on entry are checked before the first charge, every step other
  than Euclid's steps in `gcd` and `lcm`, which that bound covers, checks
  its own bound and charges before it computes, and the operands are never
  written. The one later domain test, of a negative power whose base is not
  a unit, comes after the charges of the inverse. A charge is not undone: a
  failure after a charge, of the bound of a later step, of a later charge
  (the work limit, a cancellation or the deadline), of the domain of a
  negative power or of the storage of the result, keeps the work charged
  before it, where the rule restores the state from before the operation.
- **Rule 2, no allocation at run time.** The rule is written for kernels
  whose capacities are fixed at boot. num-bigint allocates each integer at
  run time, only after a bound that covers it has been checked against
  `max_integer_bits`, and the kernel builds no collection.

The kernel is not a proof target, so the module list does not hold it.

The prime fields are written in the provable subset of the krepi convention,
its constructs R1 to R7, its loop shapes and its design rules, and are
shaped for a proof of the four kernels; they have not been extracted. The
kernels and the constructor are in `src/coefficient/prime.rs` and the
methods of the coefficient traits in its child
`src/coefficient/prime/traits.rs`: `add` and `inverse` name both a kernel
and a method of a trait, and in different files each has a key of its own in
the inventory of `cargo xtask formal check`, which rejects an inherent
method and a method of a trait with one name in one file. The kernels `add`,
`sub`, `mul` and `inverse` are pure functions of the modulus and
machine-word residues, which take no context and allocate nothing, and
`inverse` holds the only loop of the arithmetic, with no `?` and no early
return. The methods of the coefficient traits have no loop: their domain
tests, their bound checks and their charges come first, and each then
computes its result with the kernels; `from_integer` reaches the Euclidean
division of the integer kernel instead. The constructor's test calls
`modular_power`, whose num-bigint integers would be trusted external
functions; it is split into a loopless constructor that returns early, a
helper whose one loop runs over the bases and a helper whose one loop
squares, each leaving before its loop through no `?` and no `return`, and
the loop over the bases is an index loop over a constant array. Design rules
1 and 2 are met as adapted, as for the integer kernel: the domain tests and
the bound of each step come before its charge and the operands are never
written, a charge is not undone, and the integers of the test are allocated
at run time only after the bound that covers them; the arithmetic of the
residues allocates nothing.

The module list of the component, the files that the `subset` step of
`cargo xtask check` checks against the provable subset and that
`cargo xtask formal check` inventories, holds the coefficient-field trait
and the prime fields; the numbers are not listed:

```paths
src/coefficient.rs
src/coefficient
```

## Current deviations

None: the code and the tests follow every rule above.
