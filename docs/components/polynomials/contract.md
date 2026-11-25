# Polynomials

This contract states the univariate polynomials of kalyx: the ring $K[x]$ of
one variable over a coefficient ring $K$ and its polynomials; their
representation, operations, limits, storage cost and charges; and over
$\mathbb{Q}$ the expansion of a term into a polynomial, the conversion of a
polynomial back into a term and differentiation by the variable, with the
order of their failures and their tests; and the operations `expand` and
`diff` of the command entry, which expand and differentiate the input of a
request. It applies to the module `src/polynomial.rs` with its submodules in
`src/polynomial/`, and, for `expand` and `diff`, to their functions in
`src/command/dispatch.rs`. The
[architecture](../../architecture.md#coefficient-field-trait) places the
component among the components of release 0.1 and states the design rules of
the coefficient-field trait that the polynomials are built on, and the
[public API conventions](../../conventions/public-api.md) state the rules that
every public interface follows. The limits and the charges belong to the
[context](../context/contract.md), the errors to the
[errors and result states](../errors/contract.md), the coefficient-field
trait and $\mathbb{Q}$ to the [exact numbers](../numbers/contract.md), and the
terms to the [term core](../terms/contract.md).

**Status.** Implemented in `src/polynomial.rs` and `src/polynomial/`, at tier
A0 (tested); planned for tier A2 in release 0.2. Their Lean specification is
in `verification/Kalyx/Spec/Polynomials/`, and `verification/statements.json`
records the state of its statements, as
[requirements and statements](#requirements-and-statements) lists. Division
with remainder, the GCDs, modular powers, evaluation and the maps of
polynomials coefficient by coefficient, which [FLD-R08](#fld-r08),
[FLD-R09](#fld-r09), [POL-R12](#pol-r12) to [POL-R14](#pol-r14) and
[FLD-R11](#fld-r11) state, are planned for release 0.2. The polynomials are
written anew for kalyx after the design rules of the architecture: no code and
no test is taken over from the earlier implementation, which served as a
reference, so [PORTING](../../../PORTING.md) has no row for them; it records
the parts of their Lean specification that are taken over from the
specification of the earlier implementation. Their first caller in the library
is the [command entry](../command/contract.md), with its operations `expand`
and `diff`, which
[expansion and differentiation of a request](#expansion-and-differentiation-of-a-request)
states.

## Scope

- **Included.** The parent structure `PolynomialRing<K>` and the polynomial
  `Polynomial<K>`, generic over the coefficient ring, with `Rationals`, the
  field $\mathbb{Q}$, as the default, and the prime fields `PrimeField` of
  the [exact numbers](../numbers/contract.md#prime-fields) as the other
  coefficient fields of the library; the constructor of a ring and its
  accessors; zero, one, the variable $x$, constants, negation, sums,
  differences, products, powers by repeated squaring and the derivative,
  generic over the coefficient ring;
  the degree and the terms of a polynomial; the storage cost; and over
  $\mathbb{Q}$ the expansion of a term into a polynomial, including
  coefficients that cancel to 0, the conversion back to a term and the
  derivative of a term; and the executable specification of the polynomials
  (tier A2) in Lean, with its statements and the replays of its vectors, which
  also states the shared algorithms over a coefficient field, evaluation and
  the maps of polynomials coefficient by coefficient, planned for release 0.2.
- **Excluded, with their owners.**
  - Multivariate rings, monomial orders, the coefficient rings and fields
    other than $\mathbb{Q}$ and $\mathbb F_p$, and the implementation of
    `CoefficientRing` for `PolynomialRing<K>`: the coefficient fields of
    release 0.2.
  - A value that stores a ring together with a polynomial, and the check of
    such pairs, which fails with `VariableMismatch` when two rings differ:
    with the first value that stores such a pair.
  - The implementation of the shared algorithms over a coefficient field,
    division with remainder, the GCDs and modular powers, and of evaluation
    and the maps of polynomials coefficient by coefficient: release 0.2,
    planned. Their requirements are stated below, marked as planned, and the
    Lean specification of the polynomials states them already. The
    multimodular GCD over $\mathbb{Q}$, factorization and the operations of
    the command entry that call the shared algorithms: the basic polynomial
    algorithms over $\mathbb{Q}$, release 0.2.
  - Rational function fields $K(t)$ and the other coefficient-field
    extensions: release 0.4.
  - Fast multiplication: the fast arithmetic of release 0.4.
  - The output of a polynomial: the component has no display of a
    polynomial, and a result is shown through its term. The request of
    `expand` and `diff`, the order of its checks and its operand table, the
    serialization of outcomes, the one output format of the library, and the
    replay of all the [answer vectors](../../../vectors/README.md) through it
    belong to the [command entry](../command/contract.md), whose operation
    index links the section of `expand` and `diff` here.
  - Reading input text and the canonical forms of terms: the
    [parser](../syntax/contract.md) and the [term core](../terms/contract.md).

## Interface

The module `kalyx::polynomial` holds:

- `PolynomialRing<K: CoefficientRing = Rationals>`, with `Clone` and `Debug`
  where `K` has them, and
  - for every coefficient ring: the constructor
    `PolynomialRing::new(coefficients, variable, context)`, which returns
    `Result<Self>`, the accessors `coefficient_ring()` and `variable()`, and
    `storage(polynomial)`, which returns a `Storage`;
  - for every coefficient ring `K: CoefficientRing<Undecided = Infallible>`,
    with no other bound: `zero(context)`, `one(context)`,
    `generator(context)`, the polynomial $x$, `constant(value, context)`,
    `negate(a, context)`, `add(a, b, context)`, `subtract(a, b, context)`,
    `multiply(a, b, context)`, `power(a, exponent, context)` with a `u64`
    exponent and `derivative(a, context)`, each of which returns
    `Result<Polynomial<K>>`;
  - for `PolynomialRing<Rationals>`: `expand(term, context)`, which returns
    `Result<Polynomial>`, and `to_term(polynomial, context)` and
    `differentiate(term, context)`, which return `Result<Term>`;
- `Polynomial<K: CoefficientRing = Rationals>`, with the accessors
  `degree()`, which returns `Option<u64>`, `is_zero()`, `degrees()`, which
  returns `&[u64]`, and `coefficients()`, which returns `&[K::Element]`;
  `Clone`, which copies the terms, as the coefficient-field trait requires of
  its elements for the polynomial ring that is planned to implement it; and a
  shallow `Debug`, which shows the degree and the number of terms.

Every method that may allocate or iterate takes the context last, and every
operation takes the ring as `&self`
([convention 1](../../conventions/public-api.md#1-request-context-last)); the
accessors read stored values in constant time, take no context and charge
nothing. `Polynomial` implements neither `PartialEq`, `Eq`, `PartialOrd`,
`Ord` nor `Hash`, since comparing two polynomials walks their terms: the
`compile_fail` documentation test of `Polynomial` checks that `==` does not
compile (`E0369`), and tests compare the slices that the accessors return. A
second `compile_fail` documentation test, on `zero`, checks that code generic
over every `K: CoefficientRing` cannot call the operations (`E0599`). The
crate root re-exports nothing of the component.

Crate-internal items of other components that the polynomials use:
`check_name`, the rule of symbol names of the term core, which also rejects
the reserved names; and `check_width_at` and `check_bound_at` of the context,
for amounts bounded by a machine width or beyond `u64::MAX`.

## Rules

### The two types and the receiver rule

- **The parent is the receiver.** A `PolynomialRing<K>` holds the
  coefficient ring, a parent structure of the
  [coefficient-field trait](../../architecture.md#coefficient-field-trait),
  and the name of the variable. A `Polynomial<K>` holds only its terms: it
  stores neither the coefficient ring nor the variable, its fields are
  private, and only the methods of a ring build one. Every operation takes the
  ring as its receiver.
- **Polynomials belong to their ring.** The methods assume that the
  polynomials they are given belong to the receiver: built by it, or by a
  ring with the same coefficient ring and variable. They never compare rings
  and never call `same_parent`. In this release no value stores a parent
  together with an element: the conversions take the ring as their receiver
  and a term or a polynomial as their argument, and the command entry
  converts every polynomial back to a term with the ring that built it.
  A later layer that stores such a pair checks it there, and a mismatch
  fails with `VariableMismatch`, the fault of the pair check of the
  [coefficient fields](../numbers/contract.md#the-coefficient-field-trait).
- **One public type.** `Polynomial<K>` is the type of the polynomials of
  every coefficient ring: the polynomials of $\mathbb{Q}[x]$ are
  `Polynomial<Rationals>`, which is `Polynomial` through the default
  parameter, and the coefficient rings of later releases use the same type,
  not a type of their own. `PolynomialRing<Rationals>` is the entry of this
  release.
- **The coefficient ring.** The operations reach the coefficients only through
  the methods of the coefficient-field trait: the element operations, the
  zero test, and `measure`, which gives the cost of each coefficient, a part
  of the storage cost of a polynomial. They need a zero test that always
  decides, so that no term keeps a zero coefficient: they are bounded by
  `CoefficientRing<Undecided = Infallible>`, and by nothing else, neither on
  the ring nor on its elements, so the elements need no trait of their own,
  not even an equality. A coefficient ring whose zero test can be undecided
  needs a result state for an undecided coefficient, and arrives with its own
  operations.

### Representation and invariants

A polynomial is two lists of the same length: the degrees, a `u64` each, in
strictly increasing order, and the coefficients, one element of $K$ for each
degree, none of which is zero by the zero test of $K$. The zero polynomial has
no term, and the degree of any other polynomial is its last degree. Every
polynomial that a method returns keeps these invariants, so a polynomial over
a coefficient ring with canonical elements, such as $\mathbb{Q}$, has a
unique representation. The lists have one writer, which appends a term only
above the last degree and adds the cost of its coefficient, the `measure` of
the coefficient ring, to the cost of the polynomial; a term at or below the
last degree is a broken invariant, reported as `Fault(Internal)` with nothing
appended. The algorithms write a term only
after the zero test has found its coefficient not zero.

The variable of a ring is a symbol name: an ASCII letter or `_`, followed by
ASCII letters, digits and `_`, and not one of the names `pi`, `i` and
`undefined` that the [term core](../terms/contract.md#calls-and-reserved-names)
reserves for constants. `PolynomialRing::new` checks it with the check of
`Term::symbol`, so the errors are the same: `Fault(Syntax)` with the span of
the first character that a name does not allow, or an empty span at 0 for the
empty name, and `Fault(Unsupported)` with the span of the name for a reserved
name. Then it charges one unit and one per byte of the name.

### Limits

Every polynomial is checked before a method returns it, and so is every
partial sum of the rows of a product:

1. **Degree.** The degree is checked against `max_exponent`, the field that
   bounds degrees, and against the width of `i64`, the width of the exponents
   of terms, so that every degree is the exponent of a term: the effective
   bound is the smaller of `max_exponent` and $2^{63} - 1$, and an excess
   fails with `ResourceLimit`, `LimitId::Field(Exponent)`, that bound as
   `allowed`, no scope, and `LimitAmount::Required` of the degree. A product
   checks $\deg a + \deg b$, a power its exponent $k$ and then $k \deg a$, and
   the variable $x$ its degree 1, before any charge of the operation; these
   amounts are computed in checked arithmetic, and one beyond `u64::MAX`
   exceeds every limit with `LimitAmount::Bound(u64::MAX)`.
2. **Storage.** Then the storage cost of the polynomial, below, is checked
   with `check_storage(cost, LimitScope::Value)`: together with the open
   frames and the reserved temporaries it must fit `max_nodes` and
   `max_storage_bytes`, or it fails with `LimitId::Field(Nodes)` or
   `LimitId::Field(StorageBytes)` and the scope `Value`, with `Nodes` when
   both are exceeded. A component of the cost beyond `u64::MAX` exceeds every
   limit, with `LimitAmount::Bound(u64::MAX)`. The number of terms is bounded
   through this cost, at least one node per term, as the
   [architecture](../../architecture.md#limits) derives the counts of
   elements from `max_nodes`; there is no other bound on the number of terms.

There is no hidden cap
([convention 6](../../conventions/public-api.md#6-no-hidden-caps)). A
polynomial built under one context and used under another is checked against
the receiving context: its degree and its cost as part of every result built
from it, and its coefficients against `max_integer_bits` where they take part
in arithmetic, by the coefficient operations; a coefficient that is only
copied, from a term or an operand, is checked as part of the storage cost and
against `max_integer_bits` when a term is built from it.

### Storage cost

The cost of a polynomial follows the univariate formula of the
[architecture](../../architecture.md#storage-bytes), with the variable of its
ring. Write $\ell$ for the bytes of the variable name, $(n_c, b_c)$ for the
cost of a coefficient $c$, its `measure` in the coefficient ring, which is
$(1, \mathrm{rb}(c))$ for a rational,
$\mathrm{rb}(n/d) = \lvert n \rvert + \lvert d \rvert + 3$, and
$\lvert k \rvert$ for the bit length of $k$:

| Part | Nodes | Bytes |
| --- | --- | --- |
| The zero polynomial, in place of every other part | 1 | 4 |
| A term of degree 0 | $n_c$ | $b_c$ |
| A term of degree 1 | $n_c + 2$ | $b_c + \ell + 4$ |
| A term of degree $k \ge 2$ | $n_c + 4$ | $b_c + \ell + \lvert k \rvert + 12$ |
| Each addition between two terms | 1 | 4 |
| A polynomial other than zero without a term of positive degree, a constant | 0 | $\ell$ |

Over $\mathbb{Q}$ these are the parts of the architecture: a constant term
$(1, \mathrm{rb}(c))$, a linear term $(3, \mathrm{rb}(c) + \ell + 4)$ and a
term of degree $k \ge 2$ $(5, \mathrm{rb}(c) + \ell + \lvert k \rvert + 12)$,
the parts of the term $c x^k$ written out. So $x^{256} - 1$ in $x$ costs
$(7, 36)$, and a polynomial of $n \ge 2$ terms of degree at least 2 costs at
least $6n - 1$ nodes.

`storage(polynomial)` is the storage cost of a polynomial: a method of the
ring, since the cost needs the variable name, which, like `measure`, takes no
context and charges nothing. A polynomial keeps the nodes,
the bytes without the variable name and the number of names of its terms,
updated with each term as it is built, so the method takes constant time; it
stops at `u64::MAX`. The formula becomes part of the compatibility contract
with the release tag of the component.

### Operations

All operations are generic over the coefficient ring. Each charges as the
[charges](#charges) state, and each result is checked as the
[limits](#limits) state and then charged one unit.

- **Zero, one, the variable and constants.** `zero` has no term. `one` and
  `generator` take the one of $K$ for the degree 0 or 1, and `constant` takes
  a copy of the element it is given, for the degree 0; each is the zero
  polynomial when the zero test finds its coefficient zero, as in a ring
  where $1 = 0$.
- **Negation** negates each coefficient. A coefficient that is not zero has a
  negation that is not zero in every ring, so there is no zero test.
- **Sums and differences** merge the terms of both operands in increasing
  degree. Each step takes the term of lower degree, or the two terms of the
  same degree, whose coefficients are added or subtracted and tested for zero;
  a term of the subtrahend alone is negated.
- **Products.** After the degree check, the operand with fewer terms, the
  left one when they have as many, gives the rows: each of its terms $c x^d$
  forms the row $c x^d \cdot q$ of the other operand $q$, whose products of
  coefficients are tested for zero, as they can be zero in a ring with zero
  divisors. The first row is the total. A later row whose degrees all lie
  above the degree of the total is appended to it; any other is merged into it
  as a sum is. Every total is checked as a result is, without the charge of a
  result; the last total is the product.
- **Powers.** After the checks of the exponent and the degree, $a^0$ is the
  polynomial 1 for every $a$, also $0^0 = 1$. For $k \ge 1$ the power starts
  from a copy of $a$, and each bit of $k$ below its highest one, from the top,
  squares the power and, when the bit is set, multiplies it by $a$, each as a
  product. So $0^k = 0$ for $k \ge 1$. `power` does not follow
  [convention 17](../../conventions/public-api.md#17-no-implicit-conventions):
  it states $0^0 = 1$ only in its documentation, and its result does not
  name it.
- **The derivative** by the variable takes each term $c x^d$ with $d \ge 1$ to
  $(d \cdot 1) \, c \, x^{d - 1}$, where $d \cdot 1$ is the image of the
  integer $d$ by `from_integer` and the product is that of $K$, tested for
  zero; constant terms vanish. Integers enter only as $n \cdot 1$ and no
  coefficient is divided, so the derivative holds in every characteristic.

A failure of a coefficient operation, such as `ResourceLimit` naming
`max_integer_bits`, ends the operation with that error.

### Expansion

`expand(term, context)` returns the polynomial of a term in $\mathbb{Q}[x]$,
for the variable $x$ of the ring.

1. **Entry.** The depth of the term is compared with `max_depth` with
   `check(Depth, depth)` before any charge, so a term built under wider
   limits fails at once, with `LimitId::Field(Depth)`, no scope and
   `LimitAmount::Required` of its depth.
2. **Walk.** The term is walked with a stack on the heap, the children of a
   node in their stored order, which is the canonical order of the term core:
   the base of a power, the factors of a product, the cores of the monomials
   of a sum. Every occurrence of a node is entered before its children and
   charges one unit when it is entered; its polynomial is formed after those
   of its children.
3. **Polynomials of the nodes.**
   - A number is the constant of its value.
   - A symbol is compared with the variable name byte by byte, after a charge
     of one unit per byte of the shorter of the two names: the variable is the
     polynomial $x$, and any other symbol fails with `Fault(UnknownSymbol)`.
   - A power with an exponent $k \ge 0$ is the power $p^k$ of the polynomial
     $p$ of its base. A power with a negative exponent fails with
     `Fault(NotPolynomial)` when it is reached, after its base.
   - A product builds the constant of its coefficient when it is opened,
     before its first factor, and multiplies it by the polynomial of each
     factor in turn.
   - A sum builds the constant of its constant when it is opened, before its
     first core, and after each core adds to it the product of the constant
     of the coefficient of the monomial and the polynomial of its core. The
     addition takes the other when one of the two is zero, appends the
     product when all its degrees lie above the degree of the total, and
     merges as a sum otherwise; the total is a result and checked as one.
   - A call fails with `Fault(NotPolynomial)`, and so do a constant and a
     condition, the kinds that the term core plans for release 0.2: a constant
     is not a rational number, and a condition is not a value. No term of this
     release is a call, a constant or a condition.
4. **Cancellation.** Coefficients that cancel leave no term, so
   $(x + 1)^2 - x^2 - 2x - 1$, which the term core keeps as a sum of a
   constant and three monomials, expands to the zero polynomial.

**Negative powers.** A base is never a number, so a base whose expansion
succeeds holds the variable and no other symbol. Every power with a negative
exponent whose base holds the variable and no other symbol therefore fails
with `NotPolynomial`, unless an earlier failure in the order below ends the
walk: the witnesses of the term core among them, $x \cdot x^{-1}$,
$0 \cdot x^{-1}$, $(x^{-1})^0$ and the witness monomial of
$x^{-1} - x^{-1} + x$, and a base whose polynomial is a constant, such as
$((x + 1)^2 - x^2 - 2x)^{-1}$. A base that holds another symbol, with the
variable or without it as in $y^{-1}$, fails with `UnknownSymbol` first, at
that symbol.

**Order of failures.** The expansion reports the first failure in this
order, and only that one: the depth of the term; then the steps of the walk
as they occur. On entering a node comes its charge of one unit, and then for
a number its constant; for a symbol the charge of its bytes, then
`UnknownSymbol` or the polynomial $x$; for a call, a constant or a condition
`NotPolynomial`, before the arguments of a call or the operands of a
condition; and for a product or a sum the constant of its coefficient or of
its constant. Its children follow in their stored order: a product multiplies
its total by the polynomial of each factor after that factor, and a sum,
after each core, builds the constant of the coefficient of that monomial,
multiplies the polynomial of the core by it and adds the result to its total;
a power, after its base, fails with `NotPolynomial` for a negative exponent
and otherwise forms the power. Each operation of the ring makes its checks
and charges in its own order. So, in $x$:

- under `max_work = 2`, $y^2$ fails with `ResourceLimit` naming `max_work`,
  since the power is charged before its base, while $y$ fails with
  `UnknownSymbol` after the charges of its node and of its byte;
- under `max_nodes = 0`, $2y$ and $y + 1$ fail with `ResourceLimit` naming
  `max_nodes` at the constant of their coefficient or of their constant,
  before $y$;
- $(x + y)^{-1}$ fails with `UnknownSymbol`, at $y$ in its base;
- $y / x = x^{-1} y$ fails with `NotPolynomial`, since its factors are
  sorted by their bases and $x^{-1}$ comes first, while $x / y = x y^{-1}$
  fails with `UnknownSymbol`;
- $x^{-1} + y$ fails with `UnknownSymbol`, since the symbol $y$ comes before
  the power $x^{-1}$ among the cores, while $y^2 + x^{-1}$ fails with
  `NotPolynomial`;
- under `max_exponent = 50`, $x^{100} z$ fails with `ResourceLimit` naming
  `max_exponent` at the power of its first factor, and $z + x^{100}$ with
  `UnknownSymbol`.

The errors of the expansion carry no span: a term has none.

### Conversion back to terms

`to_term(polynomial, context)` returns the canonical term of a polynomial of
$\mathbb{Q}[x]$, built only through the public constructors of the term core,
which check and charge every node and keep the term canonical. Each term
$c x^k$ of the polynomial, in increasing degree, is the number $c$ for
$k = 0$, the product of $c$ and the symbol $x$ for $k = 1$, and the product
of $c$ and the power $x^k$ for $k \ge 2$; the term of the polynomial is the
sum of these, so the zero polynomial is the number 0 and a polynomial of one
term is that term. The symbol is built once, with `Term::symbol`, when the
polynomial has a term of positive degree.

The term core displays a sum with its constant first and its monomials in the
term order, so the text of `to_term` of $x^2 - 1$ is `-1 + x^2`. Results are
compared with the answers of the vectors by their canonical terms, never by
text. A term of degree beyond the width of `i64` cannot occur, since every
admitted polynomial has its degree within it; the conversion reports one as
`Fault(Internal)`.

### Differentiation

`differentiate(term, context)` returns the derivative of a term by the
variable of the ring as a term: the expansion of the term, the
[derivative](#operations) of its polynomial and the conversion of the result
back to a term, in that order, each with its checks, charges and errors.

### Charges

Every step is charged to the context. The amounts depend only on the
operands, never on the limits or the remaining work, so the same operation
charges the same work under every limits that admit it. A failed charge ends
the operation with the request failure of the charge, and nothing that it
built is returned. As the
[architecture](../../architecture.md#coefficient-field-trait) asks, the shared
algorithms charge only for their own steps, the steps of their loops and the
step that builds their result, and every operation on a coefficient charges
for itself, as its coefficient ring states; an algorithm never charges on
behalf of a coefficient operation.

| Step | Charge |
| --- | --- |
| A new ring | 1, and 1 per byte of the variable name, after the name check |
| A polynomial that an operation returns, after its checks | 1 |
| A term negated, a step of a merge, a term appended, a term of a row, a term of a derivative | 1 |
| A row of a product | 1 |
| A bit of the exponent of a power below its highest one | 1 |
| The copy with which a power $k \ge 1$ starts | 1 per term, then its result |
| The operations of the coefficient ring: `one`, `from_integer`, `negate`, `add`, `subtract`, `multiply` and `zero_test` | as the coefficient ring charges them; over $\mathbb{Q}$ one unit each, except `multiply`, which charges the product of the machine words of its operands, one unit for coefficients of at most 64 bits, and the zero test nothing |
| The checks of a degree, an exponent, a depth or a storage cost, and `measure` of the coefficient ring | none |
| A node entered by the expansion, before its children | 1 |
| A symbol entered by the expansion | 1 more per byte of the shorter of its name and the variable name |
| A term of a polynomial that is converted back | 1, then the constructors of the term core |

So, over $\mathbb{Q}$: `zero` and a constant charge 1, `one` and `generator`
2, the negation of a polynomial of $n$ terms $2n + 1$; $(x + 1) + (x + 1)$
charges 5, two steps, two additions and the result; $(x + 1)(x + 1)$ charges
15, two rows, four terms of the rows with their products, the merge of the
second row, three steps and one addition, and the result; $(x + 1)^2$ charges
19, the copy 3, the bit 1 and the squaring 15; the derivative of
$x^2 + 2x + 1$ charges 8; and the expansion of `x + 1` charges 13. Drop is
not charged.

### Traversal and stack

- **No native recursion.** The expansion is one loop over its stack. A frame
  holds owned terms, whose clones only increment a count, copied scalars, and
  the owned total of an open product or sum, never a borrowed reference; a
  register carries the polynomial of the last finished subterm to the frame
  that waits for it. The arithmetic and the conversion are loops over the
  terms of their operands, and no function of the component calls itself,
  directly or through another.
- **Depth.** The stack holds one frame for each node whose children are
  being visited, and at most one more, so at most one more frame than the
  depth of the term, which the entry bounds by `max_depth`. The native stack
  use of the expansion does not grow with the depth of a term
  ([convention 15](../../conventions/public-api.md#15-depth)): a term of depth
  100,004 expands on a stack of 2 MiB. The totals on the stack are not
  retained against the limits, as the work lists of the term core are not;
  each was checked when it was built.

### Expansion and differentiation of a request

The operations `expand` and `diff` of the
[command entry](../command/contract.md#the-dispatch-table) expand the input
of a request as a polynomial in the variable of the request and return it,
or its derivative by the variable, as a term. The signature of each reads no
role of the operand table: it reads `input`, which is required, with the
start symbol `input`, and the typed field `variable`. Each returns
`Answer::Term` and has been an operation since `v0.1.0`.

1. **The variable**, step 5 of the order of a request, is checked by
   `PolynomialRing::new` with the rule of symbol names of the term core
   before the input is read: a name that is not an ASCII letter or `_`
   followed by ASCII letters, digits and `_`, the empty name included, fails
   with `Fault(Syntax)`, and a name reserved for a constant, `pi`, `i` or
   `undefined`, with `Fault(Unsupported)`, both without a span, without a
   cause frame and before any charge. Then the ring $\mathbb{Q}[x]$ of the
   variable charges one unit and one per byte of the name. Names are
   case-sensitive, so `X` is not the variable `x`.
2. **Reading.** The entry reads `input` with `parse`; an error of the parser
   fails the operation with that error, with its span into the input and the
   entry frame of the index 0.
3. **`expand`** expands the term in the ring and converts the polynomial back
   to a term with the same ring; the result is the canonical term of the
   polynomial. **`diff`** calls `differentiate`: the expansion, the
   derivative by the variable and the conversion back to a term; the result
   is the canonical term of the derivative. Both fail as the
   [expansion](#expansion) states, in its order of failures:
   `Fault(UnknownSymbol)` for a symbol other than the variable,
   `Fault(NotPolynomial)` for a negative power, and the limits of the degree
   and of the storage of every polynomial; all without a span and with the
   entry frame of the index 0.

The result is `Settled::Value` of `Answer::Term`; neither operation ends in
a state.

### Parents and elements

`expand` and `diff` build their ring from the variable of the request and
convert the polynomial that the ring returns back to a term with that same
ring, before the operation returns; no polynomial outlives its operation,
and an outcome holds terms only. So the command entry stores no parent
together with an element, and no check of parents applies in this release.
A later release that stores such a pair, such as a polynomial in a session,
checks it there with the pair check of the
[coefficient fields](../numbers/contract.md#the-coefficient-field-trait),
which fails with `VariableMismatch` when the parents differ.

## Requirements

The identifiers `FLD-R` are those of the coefficient fields of the earlier
implementation of the casξ computer algebra system, and each such entry states
the part of the requirement that applies to the polynomials. The other
requirements of the component have no identifier there: the component numbers
them `POL-R01` to `POL-R14`, each with a name of what it states. No identifier
is ever renumbered or reused. Each entry states the requirement as kalyx
implements it, and the tests that are its evidence. [FLD-R08](#fld-r08),
[FLD-R09](#fld-r09), [POL-R12](#pol-r12) to [POL-R14](#pol-r14) and
[FLD-R11](#fld-r11) state the shared algorithms over a coefficient field,
evaluation and the maps of polynomials of release 0.2, which are planned and
not implemented yet. The Lean specification states every requirement, as
[requirements and statements](#requirements-and-statements) lists. FLD-R05,
the compatibility of parents and `VariableMismatch`, does not apply to the
polynomials in this release: no value of the component stores a parent
together with an element, as
[the two types](#the-two-types-and-the-receiver-rule) state. Tests are in
`tests/polynomials.rs` unless the entry names `src/polynomial/tests.rs`,
`tests/polynomial_properties.rs`, `src/term/tests.rs`, `tests/command.rs`
or a documentation test in `src/polynomial.rs`.

### FLD-R01

**Canonical forms.** The stored form of a polynomial is canonical: the degrees
are strictly increasing, no stored coefficient is zero, the zero polynomial
has no term, and the last degree is the degree of the polynomial, whose
coefficient is the leading coefficient. Every polynomial that a method returns
has this form, so over $\mathbb{Q}$ two polynomials are equal exactly when
their degrees and coefficients are.

- **Implemented here.** `PolynomialTerms` in `src/polynomial/terms.rs`, whose
  only writer appends a term above the last degree, and the zero tests of
  `src/polynomial/arithmetic.rs`.
- **Evidence.** Positive: `terms_expand_into_their_polynomials`. Negative:
  `coefficients_that_cancel_leave_no_term`, whose results an implementation
  that kept a zero coefficient, or did not drop a cancelled one, gets wrong.
  Also `polynomials_are_opaque_and_their_debug_view_is_shallow`,
  `powers_agree_with_repeated_products`, and in `src/polynomial/tests.rs`
  `a_term_not_above_the_last_degree_is_an_internal_fault`.

### FLD-R03

**Integer powers.** $a^0 = 1$ for every polynomial $a$, including
$0^0 = 1$, and $0^k = 0$ for $k \ge 1$. An exponent above `max_exponent`, or
a degree $k \deg a$ above it, fails with `ResourceLimit` naming it, before any
charge, and the result is checked as every result is.

- **Implemented here.** `power` in `src/polynomial/arithmetic.rs`.
- **Evidence.** Positive: `powers_agree_with_repeated_products`. Negative:
  `the_degree_is_checked_against_max_exponent_before_the_work`, with the
  exponent and the degree beyond the limit and nothing charged.

### FLD-R04

**Zero tests.** The operations rely on the zero test of the coefficient ring
to drop every term whose coefficient is zero, so they take only a coefficient
ring whose zero test always decides: `Undecided = Infallible`, as for
$\mathbb{Q}$.

- **Implemented here.** The bounds of the operations in `src/polynomial.rs`
  and `is_zero` in `src/polynomial/arithmetic.rs`.
- **Evidence.** Positive: `coefficients_that_cancel_leave_no_term`.
  Negative: the `compile_fail` documentation test of `zero`, which fails to
  call an operation for every `K: CoefficientRing` (`E0599`).

### FLD-R12

**Accounting under the request context.** The effect of every operation on
the context is a sequence of charges that stops at the first failure; the
amounts depend only on the operands, as [charges](#charges) state; an
operation that succeeds with work $w$ succeeds with the same result and work
under every budget of at least $w$, and fails with `ResourceLimit` naming
`max_work` under every smaller budget. Every result passes the checks of
[limits](#limits).

- **Implemented here.** Every charge of the component.
- **Evidence.** Positive:
  `operations_charge_the_amounts_of_the_charge_table` and
  `the_expansion_charges_its_nodes_and_the_operations_of_the_ring`.
  Negative: `every_operation_is_charged_step_by_step`, under every budget
  below the work of each operation and under wider limits. Also
  `a_cancelled_request_ends_an_operation_at_its_first_charge` and
  `products_take_their_rows_from_the_operand_with_fewer_terms`.

### POL-R01

**The ring and its variable.** A ring holds its coefficient ring and a
variable that follows the rule of symbol names; a reserved or malformed name
fails as `Term::symbol` fails, and charges nothing.

- **Implemented here.** `PolynomialRing::new` in `src/polynomial.rs`, with
  `check_name` of the term core.
- **Evidence.** `the_variable_follows_the_rule_of_symbol_names`.

### POL-R02

**The variable of a request.** The variable of `expand` and `diff` follows the
rule of symbol names and is checked before the input; `eval` does not read it.

- **Implemented here.** `ring` and `variable_error` in
  `src/command/dispatch.rs`.
- **Evidence.** `the_variable_of_expand_and_diff_follows_the_rule_of_symbol_names`,
  `names_are_case_sensitive` and
  `the_charge_of_the_variable_fails_as_a_resource_limit`, in
  `tests/command.rs`.

### POL-R03

**Limits of the degree and of the number of terms.** Every result and every
partial sum of a product is checked against `max_exponent` and, through its
storage cost, against `max_nodes` and `max_storage_bytes`, as
[limits](#limits) and [storage cost](#storage-cost) state; a polynomial is
checked against the receiving context.

- **Implemented here.** `check` and `check_degree` in
  `src/polynomial/terms.rs`, and the degree checks of products and powers in
  `src/polynomial/arithmetic.rs`.
- **Evidence.** The degree:
  `the_degree_is_checked_against_max_exponent_before_the_work`, a negative
  case with `(x^100 + 1)*(x^100 - 1)` under `max_exponent = 150`. The number
  of terms: `the_number_of_terms_is_bounded_through_the_storage_cost`, a
  negative case with $1 + x + \dots + x^9$ under `max_nodes = 40`, and the
  bytes, the reserved temporaries and a partial sum of a product. A partial
  sum above every row and the product:
  `a_product_fails_at_a_partial_sum_above_every_row_and_the_product`, with
  $(1 + x + x^2)(1 - x^2 + x^4)$ under `max_nodes = 28`. A product with zero:
  `a_product_with_zero_is_checked_as_every_result`. Also
  `the_storage_formula_of_polynomials`,
  `polynomials_are_checked_against_the_receiving_limits`, and in
  `src/polynomial/tests.rs` `the_measure_is_the_storage_formula`,
  `a_measure_beyond_u64_max_exceeds_every_limit` and
  `degrees_are_bounded_by_the_width_of_i64`.

### POL-R04

**Expansion of terms.** A term expands into its polynomial in the variable as
[expansion](#expansion) states: numbers, the variable, sums, products and
nonnegative powers; coefficients that cancel leave no term; another symbol
fails with `UnknownSymbol`, and a negative power whose base holds the
variable, the witnesses included, with `NotPolynomial`. The constants and the
conditions that the term core plans for release 0.2 fail with `NotPolynomial`,
as a call does.

- **Implemented here.** `src/polynomial/expansion.rs`.
- **Evidence.** Positive: `terms_expand_into_their_polynomials`. Negative:
  `negative_powers_whose_base_holds_the_variable_are_not_polynomials` and
  `rational_function_1_and_unknown_symbol_1_fail_with_their_faults`, the two
  cases of the vectors converted from the profiles fixture of the earlier
  implementation.

### POL-R05

**Order of failures.** A term with more than one failure fails with the first
in the [order of failures](#expansion).

- **Implemented here.** The loop of `src/polynomial/expansion.rs`, which
  enters each node before its children and charges it on entry, and the
  check of the depth before the loop.
- **Evidence.** `failures_come_in_the_order_of_the_visit`, and in
  `src/term/tests.rs` `the_expansion_into_polynomials_rejects_a_call`, which
  builds the reserved call node that only the tests of the term core can
  build.

### POL-R06

**Conversion back to terms.** A polynomial converts into its canonical term
through the constructors of the term core, which expands back into the same
polynomial under limits that admit the polynomial and the depth of its term.

- **Implemented here.** `src/polynomial/conversion.rs`.
- **Evidence.** `polynomials_convert_back_to_canonical_terms`, and in
  `src/polynomial/tests.rs`
  `a_degree_beyond_the_width_of_i64_is_an_internal_fault`.

### POL-R07

**Differentiation.** The derivative by the variable, of a polynomial and of a
term.

- **Implemented here.** `derivative` in `src/polynomial/arithmetic.rs` and
  `differentiate` in `src/polynomial.rs`.
- **Evidence.** `the_derivative_is_taken_by_the_variable`, and the
  derivatives of the answer vectors.

### POL-R08

**The answer vectors.** The 27 cases of `vectors/r02.tsv` whose operation is
`expand` or `diff` pass as host tests: the 21 expansions, 18 with an answer
and three errors, one each of `NotPolynomial`, `UnknownSymbol` and
`ResourceLimit`, and the 6 derivatives. Each runs as one request under its
limits: the input is parsed, the ring of its variable is built, and the input
is expanded and converted back, or differentiated; the result is compared with
the parsed answer through `Term::equals`, and an error by its kind and, for
`ResourceLimit`, by the field that the limits column sets.

- **Implemented here.** The whole component, with the parser and the term
  core.
- **Evidence.** `the_expand_and_diff_vectors_of_r02`.

### POL-R09

**Deep terms on a small stack.** Terms of any depth that `max_depth` admits
are expanded and differentiated with a native stack that does not grow with
their depth, and a deeper term is rejected at the entry.

- **Implemented here.** The loop and the entry check of
  `src/polynomial/expansion.rs`.
- **Evidence.** `depth_100000_chains_expand_and_differentiate_on_a_2_mib_stack`
  and `the_entry_rejects_a_term_deeper_than_max_depth`.

### POL-R10

**One shared implementation.** The arithmetic and the derivative exist once,
generic over the coefficient ring and reaching the coefficients only through
the coefficient-field trait: its element operations, its zero test and
`measure` for the cost of a coefficient. No operation places a bound on the
elements beyond the trait; the only bound beyond `CoefficientRing` is the
reason type `Infallible` of the zero test. The polynomials of every
coefficient ring have the one type `Polynomial<K>`, and later coefficient
rings use it, not a type of their own.

- **Implemented here.** `src/polynomial/arithmetic.rs` and the writer of the
  terms in `src/polynomial/terms.rs`.
- **Evidence.** `the_shared_algorithms_are_generic_over_the_coefficient_trait`,
  whose helpers are generic over every coefficient ring whose zero test
  decides, with no bound on the elements, and are instantiated with
  $\mathbb{Q}$; and the generic helpers of `tests/polynomial_properties.rs`,
  which compare coefficients only by `subtract` and `zero_test` of the
  coefficient ring.

### POL-R11

**Arithmetic against an independent reference.** Products are commutative and
associative, the product distributes over the sum, and the derivative is
linear and follows the product rule; the binomial powers $(x + 1)^n$ have the
binomial coefficients.

- **Implemented here.** `src/polynomial/arithmetic.rs`.
- **Evidence.** The property tests of
  [testing obligation 5](#testing-obligations) in
  `tests/polynomial_properties.rs`.

### FLD-R08

**Univariate division with remainder.** Planned for release 0.2: over a
coefficient field, the division of $a$ by $b$ fails with `DivisionByZero` when
$b$ is the zero polynomial, and otherwise returns the quotient $q$ and the
remainder $r$, both canonical, with $a = q b + r$ and $\deg r \lt \deg b$, two
conditions that determine them uniquely. The remainder alone is the same $r$,
and fails with `DivisionByZero` for the zero polynomial too. Like the
operations of [POL-R10](#pol-r10), the division exists once, for every
coefficient field, $\mathbb{Q}$, $\mathbb F_p$ and the number fields among
them, and reaches the coefficients only through the coefficient-field trait.
The checks and the charges of the division under the request context and the
division of multivariate polynomials are not part of this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### FLD-R09

**Monic GCDs.** Planned for release 0.2, for the polynomials of one variable
over a coefficient field: the GCD of the Euclidean algorithm is monic, with
leading coefficient 1, unless both inputs are zero; $\gcd(0, 0) = 0$,
$\gcd(p, 0)$ is the monic form of $p$, which is $p$ multiplied by the inverse
of its leading coefficient, and the GCD with a nonzero constant is 1. The GCD
divides both inputs and is divisible by every common divisor, and these
conditions determine it uniquely; two inputs are coprime exactly when their
GCD is 1. The multivariate GCD, the checks and the charges under the request
context, and the multimodular GCD over $\mathbb{Q}$, which these conditions
determine as well, are not part of this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### POL-R12

**Extended GCD.** Planned for release 0.2: over a coefficient field, the
extended Euclidean algorithm returns cofactors $s$ and $t$ and the GCD $g$ of
[FLD-R09](#fld-r09) with $s a + t b = g$, and the cofactors are those of
lowest degree:

- when $b$ is zero, $t = 0$, and $s = 0$ too when $a$ is zero, so the extended
  GCD of $0$ and $0$ is $(0, 0, 0)$ and that of $2x$ and $0$ is $(1/2, 0, x)$;
- when $b$ is a nonzero constant multiple of $g$, $s = 0$, whatever $a$ is, so
  the extended GCD of $x^2 - 1$ and $x - 1$ is $(0, 1, x - 1)$ and that of
  $2x + 2$ and $x + 1$ is $(0, 1, x + 1)$;
- when $a$ is a nonzero constant multiple of $g$ and $b$ is not, $t = 0$, so
  the extended GCD of $x + 1$ and $x^2 - 1$ is $(1, 0, x + 1)$;
- otherwise, $\deg s \lt \deg b - \deg g$ and $\deg t \lt \deg a - \deg g$.

In the first three cases $s a + t b = g$ determines the other cofactor, and in
the last the bound on $\deg s$ determines both, so the extended GCD is unique.
A variant that returns one cofactor only, the charges of the cofactors and the
operation `gcdex` of the command entry are not part of this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### POL-R13

**Modular powers.** Planned for release 0.2: over a coefficient field, the
power of $a$ to the exponent $k \ge 0$ modulo $m$ fails with `DivisionByZero`
when $m$ is the zero polynomial, and is otherwise the remainder of $a^k$ by
$m$ of [FLD-R08](#fld-r08), canonical and of degree below $\deg m$. For
$k = 0$ it is the remainder of 1, so every modular power modulo a nonzero
constant is the zero polynomial. The order of the squarings affects only the
charges; the limits of the exponent and the charges are not part of this
entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### POL-R14

**Evaluation.** Planned for release 0.2: over a coefficient ring, the value of
the polynomial $\sum_i c_i x^{d_i}$ at an element $c$ is $\sum_i c_i c^{d_i}$,
formed by the operations of the coefficient ring, with $c^0 = 1$, also for
$c = 0$. Evaluation at a point is a ring homomorphism: the value of a sum is
the sum of the values, the value of a product is the product of the values,
and the value of the polynomial 1 is 1. Evaluation at a polynomial, which is
composition, evaluation through a map into another ring, and the charges are
not part of this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### FLD-R11

**Homomorphisms.** Planned for release 0.2: a polynomial is mapped along a map
of coefficients, each edge of the homomorphism graph of the
[exact numbers](../numbers/contract.md#fld-r11), coefficient by coefficient.
When every coefficient lies in the domain of the map, the result is the
polynomial of the images, without the terms whose image is zero; otherwise it
is the result state `notInDomain`, which is not an error. Where it is defined,
the map of polynomials preserves sums and products, and a total map gives the
exact image of every polynomial. The map of an element is that of
[FLD-R11](../numbers/contract.md#fld-r11) of the exact numbers; the checks and
the charges under the request context and the maps of multivariate polynomials
are not part of this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### Requirements and statements

The Lean specification in
[`verification/Kalyx/Spec/Polynomials/`](../../../verification/Kalyx/Spec/Polynomials)
states the requirements above, written from them and from the design rules of
the architecture, not from the code: the representation with its one writer,
the storage cost and the checks of the limits, the ring operations and the
derivative, the shared algorithms over a coefficient field, evaluation, the
maps of polynomials coefficient by coefficient, and over $\mathbb{Q}$ the ring
of a variable, the expansion of a term, the conversion back to terms,
differentiation and the operations `expand` and `diff` of a request. Its
polynomials and algorithms are computable definitions over the coefficient
rings and fields of the
[specification of the exact numbers](../numbers/contract.md#requirements-and-statements),
and its terms are those of the
[specification of the term core](../terms/contract.md#requirements-and-statements);
it imports both and restates neither. The limits that its checks read,
`max_exponent`, `max_nodes`, `max_storage_bytes` and `max_depth`, are explicit
parameters, and a result is a value, a fault or `ResourceLimit`. The meaning
of a polynomial is its interpretation in the polynomials of Mathlib over the
interpretation of its coefficients; the meaning of a term, as the term core
states it, is compared with the value of a polynomial of $\mathbb{Q}[x]$ at
the value of the variable.

The properties hold for every coefficient ring of the specification of the
exact numbers whose ring laws hold and whose zero test is exact under its
interpretation, the value of evaluation already when its ring laws hold; and
those of the shared algorithms over a coefficient field, [FLD-R08](#fld-r08),
[FLD-R09](#fld-r09), [POL-R12](#pol-r12) and [POL-R13](#pol-r13), for every
coefficient field whose interpretation is a field and whose field laws hold as
well, as for $\mathbb{Q}$, $\mathbb F_p$ and the number fields.
[FLD-R12](#fld-r12) is stated for the limits that the checks read: under every
limits, an operation of a ring returns its canonical result or fails with
`ResourceLimit` naming one of them, and its examples show the same result
under wider limits and the limit that a narrower one names; the charges,
`max_work`, cancellation and the deadline are not stated. [POL-R03](#pol-r03)
is stated for the degree and the storage cost of every result and partial sum,
without the open frames and the reserved temporaries of the context and
without the saturation at `u64::MAX`; [POL-R05](#pol-r05) for the failures of
the walk and the checks, not for the charges; and [POL-R09](#pol-r09) for the
check of the depth at the entry, not for the native stack. The expansion keeps
the meaning of a term under every interpretation of its calls, conditions and
constants, and the conversion back to terms under every total order of the
term core and every lawful interpretation, the parameters of the statements
about the term core.

The propositions of
[`verification/Kalyx/Statements/Polynomials.lean`](../../../verification/Kalyx/Statements/Polynomials.lean)
are its registered statements: nine properties, and a positive and a negative
example of each requirement, which fix the default limits and the sample order
of terms unless they name others. `verification/statements.json` registers
them with the theorems of the modules in
[`verification/Kalyx/Proofs/Polynomials/`](../../../verification/Kalyx/Proofs/Polynomials)
and records the state of each.
[`verification/Kalyx/SpecTests/Polynomials.lean`](../../../verification/Kalyx/SpecTests/Polynomials.lean)
replays through the specification, with `#guard`, the 27 cases of
[POL-R08](#pol-r08) in [`vectors/r02.tsv`](../../../vectors/r02.tsv) and 20
vectors of [`vectors/cli_cases.tsv`](../../../vectors/cli_cases.tsv) and
[`vectors/library.tsv`](../../../vectors/library.tsv) whose answers the
polynomials decide: their operations `expand` and `diff`, and `divrem`, `gcd`
and `gcdex` through the shared algorithms over $\mathbb{Q}$ on the expansions
of their operands.

| Requirement | Properties | Positive example | Negative example |
| --- | --- | --- | --- |
| [FLD-R01](#fld-r01) | `RingOperationsAreExact` | `SumsKeepOneTermOrNone` | `NonCanonicalTermLists` |
| [FLD-R03](#fld-r03) | `RingOperationsAreExact` | `PowersOfZeroAndOfABinomial` | `PowersCheckTheExponentFirst` |
| [FLD-R04](#fld-r04) | `RingOperationsAreExact` | `BinomialCoefficientsVanishModuloSeven` | `ZeroDivisorsLeaveNoTerm` |
| [FLD-R12](#fld-r12) | None | `PowersAgreeUnderWiderLimits` | `ExceededLimitsNameTheirField` |
| [POL-R01](#pol-r01) | None | `RingOfAVariableName` | `ReservedAndMalformedVariables` |
| [POL-R02](#pol-r02) | None | `DerivativeByANamedVariable` | `TheVariableIsCheckedBeforeTheInput` |
| [POL-R03](#pol-r03) | None | `StorageOfASparsePolynomial` | `NodesBoundTermsAndPartialSums` |
| [POL-R04](#pol-r04) | `ExpansionKeepsMeanings` | `TermsExpandIntoPolynomials` | `ForeignSymbolsAndNegativePowersFail` |
| [POL-R05](#pol-r05) | None | `FailuresFollowTheWalk` | `OnlyTheFirstFailureIsReported` |
| [POL-R06](#pol-r06) | `ExpansionKeepsMeanings` | `PolynomialsConvertBackToTerms` | `ConversionBuildsCanonicalTerms` |
| [POL-R07](#pol-r07) | `DerivativeFollowsTheProductRule` | `DerivativesOfPolynomialsAndTerms` | `DerivativesThatVanishOrFail` |
| [POL-R08](#pol-r08) | None | `BinomialVectorExpands` | `DegreeLimitVectorFails` |
| [POL-R09](#pol-r09) | None | `TermsWithinTheDepthExpand` | `DeeperTermsFailAtTheEntry` |
| [POL-R10](#pol-r10) | `RingOperationsAreExact`, `DerivativeFollowsTheProductRule` | `OneProductForEveryCoefficientRing` | `CrossTermsVanishModuloTwo` |
| [POL-R11](#pol-r11) | `RingOperationsAreExact`, `DerivativeFollowsTheProductRule` | `BinomialCoefficientsOfAFourthPower` | `ProductOfXAndXPlusOne` |
| [FLD-R08](#fld-r08) | `DivisionWithRemainderIsUnique` | `DivisionsWithRemainder` | `DivisionByZeroAndByAHigherDegree` |
| [FLD-R09](#fld-r09) | `MonicGcdIsUnique` | `GcdsOfCommonFactors` | `GcdsWithZeroAndConstants` |
| [POL-R12](#pol-r12) | `ExtendedGcdHasLowestCofactors` | `ExtendedGcdOfAMultiple` | `ExtendedGcdsWithZero` |
| [POL-R13](#pol-r13) | `ModularPowersAreRemainders` | `ModularPowerOfX` | `ModularPowersByZeroAndConstants` |
| [POL-R14](#pol-r14) | `EvaluationIsAHomomorphism` | `EvaluationAtTwo` | `EvaluationVanishesOnAllOfSeven` |
| [FLD-R11](#fld-r11) | `MapsActOnEachCoefficient` | `IntegerPolynomialsReduceModuloSeven` | `ReductionOutsideTheDomain` |

## Testing obligations

1. **Requirements.** One positive and one negative test for each of FLD-R01,
   FLD-R03, FLD-R04 and FLD-R12, and the tests that each other entry names;
   for a planned requirement, the positive and the negative example of the
   specification that
   [requirements and statements](#requirements-and-statements) lists, until
   the implementation adds its tests.
2. **Limits.** One negative case each for the degree and the number of
   terms, each a `ResourceLimit` with its `LimitId`, the storage case with the
   scope `Value`.
3. **Faults of the vectors.** `rational_function_1` fails with
   `NotPolynomial` and `unknown_symbol_1` with `UnknownSymbol`, under their
   limits.
4. **Vectors.** The 27 `expand` and `diff` cases of `vectors/r02.tsv` pass as
   host tests, compared by canonical terms through `Term::equals`, never by
   text.
5. **Properties.** Property tests from fixed seeds in
   `tests/polynomial_properties.rs`, written by an author other than the
   author of the polynomials, through the public interface and against a
   reference written in the test code that does not call the polynomials of
   kalyx: five families of 1,000 cases each, the commutativity and the
   associativity of products, distributivity, the linearity of the derivative
   and the product rule; and $(x + 1)^n$ for $n = 0, \dots, 224$, 225 cases,
   compared coefficient by coefficient with binomial coefficients computed in
   the test.
6. **Depth.** On a thread with a stack of 2 MiB and `max_depth` above the
   depth, a chain of depth above 100,000 whose polynomial stays small expands
   and differentiates to its result, and a chain of that depth whose
   polynomial grows with it runs out of `max_work` in the middle of the
   visit; and a term deeper than `max_depth` fails at the entry before any
   charge.
7. **Generic algorithms.** A test instantiates helpers written for every
   coefficient ring whose zero test decides with $\mathbb{Q}$. The generic
   helpers of the tests take no bound on the elements beyond the trait and
   compare coefficients only by `subtract` and `zero_test` of the coefficient
   ring, never by `==`.
8. **Work.** Tests pin the charges of a few operations and expansions, and
   check that the charges do not depend on the limits and that a smaller
   budget fails; they assert no other amount.
9. **No message text.** No test asserts the message of an error; tests
   compare the kind, the span and the exceeded limit.

## Extractability

The polynomials are planned for tier A2 in release 0.2. They are written in
the style of the provable subset of Rust that the term core follows, the krepi
convention on the provable subset, so that they can join a proof target
without a rewrite; no proof target is registered for them yet, and none of
their code has been extracted.

- **Constructs.** No function item is passed as a value (R1), no
  `Iterator::any` (R2) or `Iterator::flatten` (R3) is called, and no closure is
  given to a combinator, an adapter or a parameter (R4): `match` takes the
  place of combinators, and the generic algorithms call the `&self` methods of
  the coefficient-field trait directly. No mutable borrow of an element is
  held across a write to another value; a merge step writes the merged list
  and then the cursor, through two separate parameters (R5). The enumerations
  have names that are unique in kalyx: `PolynomialSign` and `PolynomialFrame`
  (R6). R7 concerns Lean code, which the component does not have.
- **Loop shapes.** A function has at most one loop, at the top level of its
  body. A function whose loop uses `?` leaves before the loop only through
  `?`, and the one such `?`, the copy with which `raise` starts, comes when
  the function owns no value that needs dropping; checks and shortcuts that
  return early, such as the exponent 0 of a power or the choice of the rows of
  a product, are in loopless functions that call the helper with the loop.
  The terms are walked by index loops and the expansion by `while let` over
  `Vec::pop`; no loop condition is a macro. The zero test unwraps the
  uninhabited reason of an undecided answer with an empty `match`, the shape
  that the records cover.
- **Frames and state.** The frames of the expansion, `PolynomialFrame`, hold
  owned terms, copied scalars and owned polynomials, and the register is an
  owned `Option`; no frame and no structure has a lifetime parameter, and the
  parent `PolynomialRing` has none either.
- **Integer conversions.** `usize` to `u64` is an `as` cast, which loses
  nothing on the 64-bit targets that the library supports; a nonnegative
  `i64` exponent becomes a `u64` by an `as` cast after its sign test, and a
  degree becomes an `i64` exponent by an `as` cast after the check against the
  width of `i64`. Sums and products of degrees use `checked_add` and
  `checked_mul`, and the bit length of a degree is a `const fn` loop. No
  `try_from`, `unsigned_abs` or `From` conversion between machine integers is
  used; a degree enters the coefficient ring as `Integer::from` of a `u64`.
- **Design rules.** The checks of a degree, an exponent, a depth and the
  name of the variable come before the charges of their operation, the checks
  of a result before its charge and before it is returned, and the order
  check of a term before the term is appended (1). The lists of terms, the
  rows, the totals and the stack of the expansion are allocated at run time,
  bounded by the operands and by charged steps; rules 2 and 3 are written for
  kernels and do not apply. Every loop step is charged, the bytes of the
  comparison of a name before the comparison runs, except the loops of
  `bit_length` and `highest_bit`, of at most 64 steps, and the check of the
  variable name in `PolynomialRing::new`, which reads the name before its
  charge, so that a rejected name charges nothing, as in the term core (4). The measure of the storage cost is a field of the list of terms (5).
  The fields of both types are private, and a `compile_fail` documentation
  test keeps `Polynomial` without `==` (6). The only `cfg` is `#[cfg(test)]`
  on the unit-test module and on the module that holds `push_with_cost`, the
  writer of terms with a given cost with which the unit tests reach amounts
  beyond `u64::MAX` (7). There is no `Cell` or `RefCell` (8), and the
  library forbids `unsafe` code (9).
- **External declarations.** No code has been extracted, so this list follows
  the records that the [term core](../terms/contract.md#extractability)
  cites. Recorded as external: `Vec::pop`, `Vec::is_empty`, `str::len` and
  `str::as_bytes`. Recorded as translated with library models: `Vec::push`,
  slice indexing and `len` of `Vec` and slices. The machine-integer
  operations, `checked_add`, `checked_mul` and `saturating_add` on `u64` and
  `saturating_add` on `usize`, are not recorded as external, as for the term
  core. Not recorded: `Vec::new`, `Vec::with_capacity`, `Vec::clone`,
  `slice::get`, `slice::first`, the `vec!` macro, `Option::take`,
  `Option::replace`, `Box<str>` from a `&str`, and `std::convert::Infallible`,
  where the recorded empty `match` unwraps an empty enumeration of its own
  crate. An extraction also needs the methods of the coefficient-field
  trait, `measure` among them, `Clone` of the elements, `Integer::from`, the context
  methods `charge`, `check`, `check_storage`, `check_width_at` and
  `check_bound_at` with `Storage::new`, the constructors and accessors of the
  term core and its `check_name`; `Clone` and `Drop` of `Term`, a handle to a
  shared node that the expansion clones and its frames own, through the
  structure model of `Rc` that the term core names; and `Error::new`, whose
  string literals each add a `decide +native` axiom. `Debug` uses
  `fmt::Formatter::debug_struct`; it is not part of the arithmetic.

The module list of the component, the files that the `subset` step of
`cargo xtask check` checks against the provable subset and that
`cargo xtask formal check` inventories, holds the polynomials with their
submodules:

```paths
src/polynomial.rs
src/polynomial
```

## Current deviations

None: the code and the tests follow every rule above.
