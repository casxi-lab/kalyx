# Architecture

This document lists the components of the kalyx library, the verification
tier that each is to reach and its first production caller, and states the
design rules of four foundations that every later part builds on: the term
representation, the coefficient-field trait, the context and the error
kinds. The interface conventions that all public items follow are in
[the public API conventions](conventions/public-api.md).

**Status.** kalyx ships the errors and result states, the context and
limits, the exact numbers with the coefficient-field trait over
$\mathbb{Q}$, a command-line program without commands and the repository
checks. The errors and result states, the context and limits, and the exact
numbers with the two layers of the coefficient-field trait and `Rationals`
are implemented, each with its contract
([errors](components/errors/contract.md),
[context](components/context/contract.md),
[numbers](components/numbers/contract.md)); no other library component below
is implemented yet. For the other components, the tables are the plan and the
design rules are the rules that their code follows when it lands; each
component also gets its own `contract.md` with its requirements at that time.
Where a rule is already enforced by `cargo xtask check`, the text says so.

## Verification tiers

Each component is given a verification tier by its role. The tiers are
cumulative:

- **A0, tested.** Unit, property and integration tests, and replay of the
  answer vectors taken from the earlier implementation, run by continuous
  integration.
- **A1, tested with a written contract.** A0, plus the component's
  requirements and `contract.md`, contract tests with negative examples, and
  fuzzing of untrusted input.
- **A2, specification checked.** A1, plus an executable specification in
  Lean 4 with a property layer, one positive and one negative specification
  test per requirement, replay of the vectors against the specification, and
  differential random tests for components that are decided to be promoted.
  There is no refinement proof: an A2 component is described as
  "specification checked", never as "verified".
- **A3, implementation proved.** A2, plus Lean definitions that Charon and
  Aeneas generate from the Rust code and that are proved to refine the A2
  specification, checked by the proof gate with receipts.

The level A4, for composition and system properties, is not yet assigned to
any kalyx component. The rules for the tiers are:

- Features close at A0 or A1, on tests and vector replay; no feature depends
  on a proof. Proofs are planned only for foundations.
- Release 0.1 has only A0 and A1. It has no Lean project and no proof gate.
- A2 is recorded only once kalyx is connected to the proof tooling that it
  takes from krepi (statement hashes and the specification label); before
  that, Lean drafts count as A1.
- A3 is an upgrade after a component has closed, and only for a pure core:
  a state machine or computation without interior mutability, without
  `unsafe` and without dependence on the standard library, which was already
  proved in the earlier implementation and is taken over with its code
  essentially unchanged. The proof is done again in kalyx. A3 is postponed
  only while the proof tools are not in place, and every postponed
  obligation names the release that takes it over, no later than the next
  one.
- Code of a component planned for A2 or A3 is written in the provable subset
  of Rust ([AGENTS](../AGENTS.md)) from its first change.
- The release notes of each version tag state, for every component, its tier
  and the number of open obligations. They never call an A2 component
  verified.

## Components

The first production caller is the first code outside the component that
uses it in a release: another kalyx component, or the job of the casξ
operating system, krepi, that runs kalyx. A foundation part that has no
caller in the planned releases is not delivered early; foundation modules
land as a public interface with contract tests. Exceptions are listed here.
The one listed exception is the function registry, which fixes all its slots
at once in 0.2.

### Release 0.1

| Component | Tier | A3 upgrade | First production caller |
| --- | --- | --- | --- |
| Repository checks and guard (available today) | A0 | none | not applicable: they check the repository |
| Answer vectors taken from the earlier implementation | A0 | none | not applicable: test infrastructure |
| Errors and result states (`Error`, `Settled<T>`; implemented, [contract](components/errors/contract.md)) | A1 | 0.2, for the result-state core | the context, in 0.1 |
| Context and limits (`Context`, `Limits`; implemented, [contract](components/context/contract.md)) | A1 | 0.2, for the charging core; the frame table first needs proof models of `Vec` and `Box` | exact numbers and the coefficient-field trait over $\mathbb{Q}$, then the term core, the parser and the command entry, in 0.1 |
| Exact numbers and the coefficient-field trait over $\mathbb{Q}$ (`number`, `coefficient`; implemented, with the polynomial ring still planned, [contract](components/numbers/contract.md)) | A0; the coefficient-field interface is planned for A2 in 0.2 | none | the term core and the polynomials over $\mathbb{Q}$, in 0.1 |
| Term core and canonical forms | A1; canonical forms are planned for A2 in 0.2 | none | the parser and the command entry, in 0.1 |
| Parser | A1 | none | the command entry, in 0.1 |
| Univariate polynomials over $\mathbb{Q}$ with expansion and differentiation | A0; planned for A2 in 0.2 | none | the command entry (`expand`, `diff`), in 0.1 |
| Command entry and output serialization | A1 | none | the command-line program, in 0.1; the calculator job of krepi, built from a pinned 0.1 commit |
| Command-line program | A0 | none | none: it is the top level |

### Later foundations

These foundations are planned for later releases. Their tiers are filled in
when each release is planned, except where the plan already fixes them.

| Component | Release | Planned tiers | First production caller |
| --- | --- | --- | --- |
| Term core extension: function-call nodes and assumptions | 0.2 | A2 for canonical forms | the function-expression baseline (elementary functions, $\pi$, $i$, `undefined`), 0.2 |
| Coefficient fields beyond $\mathbb{Q}[x]$: integer kernel, $\mathbb F_p$, $\mathbb{Z}$, $\mathbb{Q}(a)$, multivariate rings, monomial orders, homomorphisms | 0.2 | A2 for the interface; A3 upgrades in 0.2 for prime fields and monomial orders | real root isolation and algebraic numbers, and basic polynomial algorithms over $\mathbb{Q}$, 0.2 |
| Function registry | 0.2 | A3 upgrade in 0.2 | the function-expression baseline, Taylor series and derivatives of function expressions, 0.2 |
| Shared result types: `Completeness`, `Evidence`; then `Guarantee` | 0.2; `Guarantee` in 0.3 | set when planned | root lists and real sets (`Completeness`), zero tests of algebraic numbers and assumption queries (`Evidence`), 0.2; numerical evaluation (`Guarantee`), 0.3 |
| Numerical kernel and evaluation framework: rational-endpoint intervals, complex balls, summation, elementary kernels, one precision driver | 0.3 | A2 for inclusion; A1 for the framework; A3 upgrade in 0.3 for the series summer | the numerical evaluation entries `precision`, `ball`, `round` and `approx`, 0.3 |
| Collection values and controlled iteration | 0.3 | A3 upgrade in 0.3 for the collection tree and text | user functions, programs and the session, 0.3 |
| Value model | 0.3 | A2 | every value kind of 0.1 to 0.3, 0.3 |
| binary64 scalars: error-free transformations, outward-rounded intervals, double-double, reproducible elementary functions, conversion between rationals and binary64 | 0.3 | A3 upgrades in 0.3 for four scalar cores | the calculator job of krepi, built from the 0.3 release, which runs bit-exact scalar fixtures |
| Stable value encoding and digests | 0.3 | A2 | typed session values and the cache key of the command layer, 0.3 |
| Coefficient-field extensions: $K(t)$, arbitrary-precision prime and extension fields, matrices over $\mathbb{Z}$ and $K[x]$, differential towers | 0.4 | set when planned | the algebra and number theory features, 0.4 |
| Fast arithmetic: multimodular methods, CRT and rational reconstruction, fast polynomial multiplication and division, half-GCD | 0.4 | A2 for CRT and rational reconstruction; A1 for the rest | polynomial factorization and GCD, 0.4 |
| Evaluator families: asymptotic expansion, recurrences and continued fractions, binary splitting, hypergeometric evaluation | 0.5 | set when planned | the special functions, 0.5 |
| Rewriting engine | 0.5 | A2 | simplification and symbolic calculus, 0.5 |
| binary64 matrices and the a-posteriori verification bridge | 0.6 | A1; A3 upgrade in 0.6 for the matrix entries | numerical linear algebra, 0.6 |
| Environment snapshot format | 1.0 | set when planned | persistent sessions, 1.0 |

## Term representation

**Status:** planned for 0.1; not implemented. The rules below are the
invariants that the term core and its contract follow.

### One shared immutable tree

There is one term type, `Term`, and every operation (parsing,
canonicalization, expansion, differentiation) produces it. A `Term` is a
shared immutable tree: a reference-counted node, `Term(Rc<Node>)`, with
private fields. A node holds its kind, its children as a `Vec<Term>`, and
cached values: the tree size, the depth, the logical bytes and whether the
term holds a power with a negative exponent. A node never changes after it is
built.

Cloning a term is $O(1)$ and subterms may be shared, but sharing is invisible:
equality and ordering compare structure and never use `Rc::ptr_eq`, and
there is no intern table and no hash container. A term is an independent
value, so it can be stored in collection values, sessions and encodings
without carrying a store along. `Rc` is not `Send`; if terms ever cross
threads, the private node pointer becomes an `Arc`, and nothing public
changes.

### Traversal and drop

Comparison, display, the collection of negative-exponent bases and
rebuilding are each a loop over a stack on the heap; none recurses natively.
Their frames hold owned terms (a clone only increments a count) and copied
scalars, never borrowed references. `Drop` for a node moves its children onto
a stack of its own and releases them one at a time with `Rc::try_unwrap`, so
dropping a deep term uses a constant amount of native stack. The native stack
use of term operations therefore does not grow with the depth of the term.

### Kinds and order

| Kind | Rank |
| --- | --- |
| Number | 0 |
| Constant (reserved for $\pi$, $i$ and algebraic numbers) | 1 |
| Symbol | 2 |
| Call (reserved for function calls) | 3 |
| Power | 4 |
| Product | 5 |
| Sum | 6 |

A new kind takes a new rank and never changes the relative order of the
existing kinds. Terms are totally ordered by rank first. Within a rank:

- numbers by value;
- symbols by their UTF-8 bytes;
- calls by the bytes of the head name, the head class, the arguments one by
  one, and the number of arguments;
- powers by base, then exponent;
- products by their factors one by one, the number of factors, then the
  coefficient;
- sums by their monomials one by one (core, then coefficient), the number of
  monomials, then the constant.

Comparison is structural, and each step is charged.

### Canonical forms

The constructors keep every term in canonical form:

- **Products.** Nested products are flattened, and numeric coefficients are
  multiplied exactly. Factors with the same base and the same sign of
  exponent are merged by adding exponents; factors with exponents of opposite
  sign are not merged. Factors are sorted, and a product contains no number
  and no product as a factor. A product with coefficient 1 and a single
  factor is that factor.
- **Powers.** The exponent is an integer. A numeric base is evaluated
  strictly, and the exponent limit is checked before the value is computed.
  An exponent of 1 returns the base. An integer power distributes over a
  product, $(c \prod f)^k = c^k \prod f^k$. A power of a power $(b^j)^k$
  becomes $b^{jk}$ only when $jk \lt 0$, when $j, k \ge 0$, or when $j = 0$.
  A power of a sum is not expanded.
- **Sums.** Nested sums are flattened, and monomials with the same core add
  their coefficients. A sum core whose coefficient becomes 1 is flattened
  again, repeatedly, so no monomial core of a sum is a sum with coefficient 1.
  A numeric scalar does not distribute over a sum: $2(x + y)$ is a single
  monomial, and distributing it is the job of `expand`.

The canonical form does not depend on the order in which a term was built:
under associativity and commutativity the result is the same, and rebuilding
a canonical term gives a structurally equal term.

### Strict numeric evaluation

Numeric subterms are evaluated when they are built, so an invalid numeric
subterm fails at once and cannot be absorbed by the term around it:

- $0^0 = 1$;
- $0^{-1}$ fails with `DivisionByZero`, and so does every negative power of
  zero;
- $1/0$ fails when it is built, so $0 \cdot (1/0)$ and $(1/0)^0$ fail with
  `DivisionByZero` as well;
- under the default limits, $x / x^{2^{32}}$ fails with `ResourceLimit` on
  `max_exponent` before any large value is built.

### Negative-exponent invariant

Write $N(t)$ for the set of bases that occur with a negative exponent in a
term $t$, and $\max N(t)$ for those elements of $N(t)$ that do not themselves
occur with a negative exponent inside another element. Canonicalization
never shrinks this set:

```math
N(\mathrm{input}) \subseteq N(\mathrm{output})
```

A canonical form therefore never hides a point where its input is undefined.
Where a simplification would lose a base, the term keeps a witness instead:

- a product whose coefficient is 0 is $0 \cdot \prod_{b \in \max N} b^{-1}$,
  and the number 0 when the set is empty;
- when $N(t)$ is not empty, $t^0$ is $\prod_{b \in \max N(t)} (b^{-1})^0$;
- in a sum, monomials that cancel to zero leave the bases that the remaining
  monomials do not cover in a single witness monomial with coefficient 0;
- in a product, a witness factor with exponent 0 is dropped when the other
  factors already cover its base;
- a witness $(b^{-1})^0$ raised to any integer power is the witness itself,
  so $((x^{-1})^0)^{-1} = (x^{-1})^0$.

So $x^2 x^{-1}$, $x x^{-1}$, $(x^{-1})^{-1}$, $0 \cdot x^{-1}$ and
$(x^{-1})^0$ each stay as written, while $x^{-1} x^{-2} = x^{-3}$. Removing
negative exponents under conditions is an explicit operation, never part of a
constructor.

### Call nodes

Function calls arrive in 0.2, but their shape and place are fixed now so
that the canonical forms of 0.1 terms do not change when they arrive. A call
is `Call(Head { name, class }, args)`. The class is `Registered` or `Formal`
and is `#[non_exhaustive]`; the arguments are canonical terms in their given
order and are not sorted. Calls are ordered by head name, not by registry
index, so registering a new function never reorders existing calls.

A call is an atom for the rules of sums, products and powers: it can be a
base or a monomial core and is never expanded. Simplification that involves
calls happens only in the call constructor, or with the call head as its
trigger, and the factors and monomials that it produces return to the same
merging worklist. The 0.1 constructors never produce a call from input
without calls, so the canonical form and the order of a call-free term do not
depend on any rule about calls.

### Reserved names

`pi`, `i` and `undefined` are reserved for constants. In 0.1 the parser and
`Term::symbol` reject them with `Unsupported`, as they reject function-call
syntax. An input accepted by 0.1 therefore keeps its meaning and its
canonical form when the constants arrive; otherwise $i \cdot i$ would change
from $i^2$ to $-1$, and the rank of `pi` from 2 to 1. Later constant names
are taken only from this list or from spellings that are errors in 0.1.

### Size and depth

- The node count of a term is its tree size: a shared subterm counts once for
  each occurrence. Its logical bytes follow the term formula of
  [the context](#storage-bytes).
- Before a term is built, its cost is checked with `check_storage` in scope
  `Value`: the costs of the open frames, the reserved temporaries and the new
  term together must fit `max_nodes` and `max_storage_bytes`. Otherwise the
  construction fails with `LimitId::Field(Nodes)` or
  `LimitId::Field(StorageBytes)`, and with `Nodes` when both are exceeded.
  The size of one value is a special case of this total; there is no separate
  limit on a single value.
- The depth of a new node is one more than the largest depth of its
  children. It is compared with `max_depth` before the node is allocated, and
  exceeding it fails with `LimitId::Field(Depth)`.
- Every step is charged, including rescans and the collection loops, which
  are charged per monomial they pass. There is no hidden cap, and a broken
  internal invariant returns an `Internal` error.

## Coefficient-field trait

**Status:** the two traits `CoefficientRing` and `CoefficientField`,
`ZeroTest` and `Rationals` are implemented in
`src/coefficient.rs`, over the exact numbers of `src/number.rs`; their
[contract](components/numbers/contract.md) states the checks, the charges and
the tests. `PolynomialRing` and `Polynomial` are planned for 0.1, with the
polynomials over $\mathbb{Q}$. `Context` and `Result` are those of
[the context](#context-api) and [the errors](#error-kinds), and `Integer` is
the library's exact integer, `kalyx::number::Integer`.

```rust
pub enum ZeroTest<U> { Zero, Nonzero, Undecided(U) }

pub trait CoefficientRing: sealed::Sealed {
    type Element: Clone;   // no Eq: non-canonical certificates can be elements
    type Undecided;        // std::convert::Infallible for exact fields
    fn same_parent(&self, other: &Self, context: &mut Context) -> Result<bool>;
    fn zero(&self, context: &mut Context) -> Result<Self::Element>;
    fn one(&self, context: &mut Context) -> Result<Self::Element>;
    fn from_integer(&self, n: &Integer, context: &mut Context) -> Result<Self::Element>;
    fn negate(&self, a: &Self::Element, context: &mut Context) -> Result<Self::Element>;
    fn add(&self, a: &Self::Element, b: &Self::Element, context: &mut Context)
        -> Result<Self::Element>;
    // subtract and multiply have the shape of add
    fn zero_test(&self, a: &Self::Element, context: &mut Context)
        -> Result<ZeroTest<Self::Undecided>>;
}

pub trait CoefficientField: CoefficientRing {
    // zero fails with DivisionByZero; divide has no default method
    fn inverse(&self, a: &Self::Element, context: &mut Context) -> Result<Self::Element>;
    fn divide(&self, a: &Self::Element, b: &Self::Element, context: &mut Context)
        -> Result<Self::Element>;
}

pub struct PolynomialRing<K: CoefficientRing = Rationals> {
    // private: the coefficient structure K and the variable
}

pub struct Polynomial<K: CoefficientRing = Rationals> {
    // private: the terms only
}
```

- **The parent structure implements the trait.** A trait is implemented by a
  value that describes the ring or field, its parent structure, and the
  elements are its associated type. $\mathbb{Q}$ is the zero-sized type
  `Rationals`, whose elements are the library's checked `Rational`. Fields
  defined by runtime data (a modulus, a minimal polynomial, the variable of
  $K(t)$) have the same shape, and elements do not repeat their parent.
- **Two layers.** `CoefficientRing` and `CoefficientField`. Division
  algorithms are bounded by `CoefficientField`, so they cannot be called on a
  ring that is not a field. $\mathbb{Z}$ and $\mathbb{Z}/n$ implement only
  `CoefficientRing`, with result-state subtraits for division that may fail:
  exact division returns a quotient or "inexact", and a unit inverse returns
  the inverse or "not a unit" with a divisor. Division with remainder and GCD
  are bounded by `CoefficientField`.
- **The zero test is required.** `zero_test` is part of the base trait;
  there is no optional zero-test subtrait. Its result `ZeroTest` is the one
  enum that is not `#[non_exhaustive]`, since its three cases are complete.
  A field whose zero test cannot always decide names its reason as the
  associated type `Undecided`.
- **Closed until 1.0.** The trait is sealed, so required methods can be added
  in later releases without breaking callers. Until 1.0, users cannot define
  their own coefficient fields.
- **Charging.** Each method takes the context last. Element operations check
  sizes before they work and charge for themselves. Shared algorithms
  (multiplication, powers by repeated squaring, differentiation, evaluation,
  and later division with remainder, GCD and modular powers) charge only for
  their own loop steps. Every amount depends only on the operands.
- **Division by zero.** In every field, `inverse` and `divide` fail with
  `DivisionByZero` on zero. A field with a structural zero test checks the
  divisor before any charge of the operation, and a field whose zero test is
  charged pays for the test first.
- **One shared implementation.** Differentiation, evaluation, powers and
  modular powers exist once, bounded by the trait. Shared code obtains
  integers only as $n \cdot 1$ and never divides by an integer, so it stays
  correct in characteristic $p$.
- **The parent is the receiver.** Polynomial operations take
  `PolynomialRing<K>`, which holds the coefficient structure and the
  variable, as `&self`. A `Polynomial<K>` stores neither, and its type is
  opaque: polynomials are produced only by methods of their ring, and these
  methods assume that their arguments belong to `self`. Whether two parents
  match is checked with `same_parent` only where a parent and an element are
  stored as a pair: when converting between terms and polynomials, in the
  command entry, and later in typed collection columns; a mismatch fails with
  `VariableMismatch`, a fault kind that arrives in 0.2 together with the
  first parents that can differ; in 0.1 the only parent is
  `PolynomialRing<Rationals>`. So a parent parametrized at runtime, such as
  $\mathbb F_p$, needs no change of signature, and polynomial operations do
  not compare parents.
- **Later structures** take the same shape: a prime field
  `PrimeField { modulus }` whose constructor checks primality; number fields,
  including $\mathbb{Q}(a)$, whose `same_parent` compares the defining data
  and is charged; `FractionField<K>` with
  `K: CoefficientField<Undecided = Infallible>`; `MultivariateRing<K>`; and
  polynomial rings, which implement `CoefficientRing` with
  `Element = Polynomial<K>`. Maps between structures form a separate trait
  over two parents, and an argument outside the domain of a map is a result
  state, not an error. Interval and ball types do not satisfy the ring
  axioms and never implement `CoefficientRing`; they are targets of maps
  only.
- **Shape for proofs.** Associated types and `&self` methods; an
  implementation never calls a default method of the same trait on `self`;
  parent structures have no lifetime parameters; no closures as callbacks.
- **What 0.1 delivers.** The two traits, `Rationals`,
  `PolynomialRing<Rationals>` with its inherent methods, and
  `Polynomial<K = Rationals>`. The other subtraits and structures, and the
  implementation of `CoefficientRing` for `PolynomialRing<K>`, arrive with
  their first users from 0.2 on.

## Context API

**Status:** implemented in `src/context.rs`; its
[contract](components/context/contract.md) states the requirements, the
reading interval of the clock, the overrun bound after a deadline and the
tests. The guard of `cargo xtask check` rejects constructing the context
outside `src/main.rs`, `src/command.rs` and `src/command/`, and every path
that starts with `Context::` elsewhere. `mark` and `restore`, described
below, are not part of this release.

### Limits

`Limits` has nine fields, each with a default; `Limits::new()` and
`Limits::default()` give the defaults, and a `with_<field>` method sets one
field. A compile-time assertion keeps the number of fields at ten or fewer,
which leaves one free field for a future limit. Each field bounds exactly one
quantity.

| Field | Bounds | Default |
| --- | --- | --- |
| `max_work` | work units charged by the request | 100000 |
| `max_input_bytes` | bytes of the request's input | 65536 |
| `max_output_bytes` | bytes of all display and serialization of the request, cumulative | 65536 |
| `max_depth` | nesting depth of syntax, terms and values | 128 |
| `max_nodes` | nodes retained at one time: the costs of the open frames, the reserved temporaries and the value being admitted | 8192 |
| `max_storage_bytes` | logical storage bytes retained at one time, over the same parts as `max_nodes` | 262144 |
| `max_integer_bits` | bits of one integer | 4096 |
| `max_exponent` | absolute value of one integer exponent; also degrees and orders of derivatives | 4096 |
| `max_frames` | frames open at one time | 32 |

The scale limits of features are derived from these fields, never written as
constants:

- degrees, orders and powers from `max_exponent`;
- the number of terms, collection elements, matrix cells and temporary
  elements from `max_nodes`, at least one node per element: a count is
  checked as `check_storage(Storage::new(count, 0), LimitScope::Value)`, or
  with the cost of its value kind when that kind has a formula, so open
  frames and temporaries count as well;
- the logical bytes of a value, a frame cost or a temporary from
  `max_storage_bytes`;
- the bits of a working precision from `max_integer_bits`;
- nested commands and user calls from `max_frames`.

A bound that is not one of these is an explicit parameter of the request, and
exceeding it fails with `ResourceLimit` naming the parameter. An iteration
cap is a parameter of its method, and reaching it is a result state
([convention 7](conventions/public-api.md#7-iteration-caps-are-result-states)).
There is no separate limit on the number of elements, since `max_nodes`
bounds it. `max_output_bytes` is a field of its own because output bytes
cannot be derived from nodes; its default is no larger than that of
`max_work`, so under the default limits output hits its own limit first.
`max_storage_bytes` measures logical bytes, computed from bit lengths, not the
memory that a value occupies; the host, such as a krepi job, bounds real
memory.

### Storage bytes

The cost of a retained value is a `Storage { nodes, bytes }`. Each value kind
implements `StorageCost` with one formula that depends only on the value,
never on the platform or the memory layout; the context receives computed
costs and never computes a formula or calls back. Write $\lvert x \rvert$ for
the bit length of an integer $x$ and $\ell$ for the length in bytes of a
symbol name.

- A rational $n/d$ costs $(1, \lvert n \rvert + \lvert d \rvert + 3)$
  wherever it occurs.
- A term costs its tree size in nodes; coefficients, constants and exponents
  stored in a node add no nodes. Its bytes are those of its canonical binary
  rendering: a number counts as a rational, a symbol $\ell$, and each binary
  sum, product or power 4. In the rendering, a product writes its
  coefficient as a factor unless it is 1; a sum writes its constant as a
  summand unless it is 0; a monomial with coefficient 1 is its core,
  otherwise the product of coefficient and core; a sum or product of $m$
  operands has $m - 1$ operators; a power has two operands. So
  $c x^k$ with $c \ne 1$ and $k \ge 2$ costs
  $\mathrm{rb}(c) + \ell + \lvert k \rvert + 12$ bytes, where $\mathrm{rb}(c)$
  is the byte cost of the rational $c$, and $xy$ costs
  $\ell_x + \ell_y + 4$.
- A univariate polynomial costs $(1, 4)$ when it is zero; otherwise each
  constant term $(1, \mathrm{rb}(c))$, each linear term
  $(3, \mathrm{rb}(c) + \ell + 4)$, each term of degree $k \ge 2$
  $(5, \mathrm{rb}(c) + \ell + \lvert k \rvert + 12)$, each addition between
  terms $(1, 4)$, and, when no term has positive degree, the variable name
  once more $(0, \ell)$. The variable is the one of its `PolynomialRing`.
  The number of terms of a polynomial is bounded through this cost.
- The formulas for integer results and number-field elements are fixed with
  them in 0.2; strings, lists, records and session bindings in 0.3, where the
  value encoding uses the same formulas; matrices in 0.4.

A formula becomes part of the compatibility contract with the release tag of
its component. Changing one changes which limit is reached first, so it is a
change of the answer vectors, made on purpose.

### Charging, the clock and cancellation

- **Charging is deterministic.** The amount of a charge depends only on the
  operands, never on the limits or the remaining budget. Each charge polls
  cancellation first, then the deadline, then checks the work limit, and
  records the work only if all three pass; a failed charge changes only the
  polling state. When several request failures hold at one charge point,
  they are reported in the order cancellation, deadline, work.
- **Reading the clock.** A charge reads the clock when it is the first charge
  after a deadline was set, when its amount is zero, when its amount is at
  least 64 units (before the work starts), when it follows such a large
  charge, and when it follows 63 consecutive small charges. When the work
  limit is exhausted, the clock is read once more, and an expired deadline
  takes precedence over exhausted work.
- **Overrun after the deadline.** The work done after the deadline passes,
  before the request fails with `DeadlineExceeded`, is at most
  $\max(4032, L)$ units plus one primitive that is running, where $L$ is the
  amount of the last large charge that read the clock before the deadline,
  and $L \le$ `max_work`. The contract of the context states this bound.
- **Injection.** `Clock::now()` returns nanoseconds as `u64`, and
  `CancelProbe::is_cancelled()` is polled first at every charge. Both traits
  keep a `fork()` method for later sub-budgets. The defaults are
  `MonotonicClock`, based on `std::time::Instant`, and `CancelFlag`, based on
  `Arc<AtomicBool>`, held in an opaque `Observer` adapter. Tests use only a
  fake clock and a fake probe; there are no test hooks inside charging. If the
  proof tools cannot translate the boxed adapter, the context becomes generic
  over its observer, and these rules stay the same.
- **Bounded output.** `charge_output(bytes)` first checks the request's
  cumulative `max_output_bytes`, then charges one work unit per byte. A
  caller writes bytes only after all their charges succeed, so there is no
  partial output.

### Frames and temporaries

The context keeps one frame table, allocated at the first frame, with one
entry per open frame: its cost as a `Storage` and its generation number. Two
plain fields hold the sum of the frame costs, `frames_total`, and the sum of
the reserved temporaries. The contract states two invariants:
`frames_total` equals the sum of the costs in the table, and `frames_total`
plus the temporaries stays within `max_nodes` and `max_storage_bytes` in each
component.

| Operation | Charge | Check | Effect |
| --- | --- | --- | --- |
| `enter_frame()` | 1 unit | the open frames are fewer than `max_frames`; otherwise `Field(Frames)`, no scope | opens a frame of cost zero and returns a `Frame` token |
| `set_frame_cost(&frame, cost)` | 1 unit | `frames_total` minus the frame's old cost, plus the temporaries and `cost`; scope `Frame` | replaces the cost of any open frame |
| `reserve(cost)` | none; not a charge point | `frames_total`, the temporaries and `cost`; scope `Temporary` | returns a `Reserved` token |
| `release(reserved)` | none | none | returns the reservation |
| `leave_frame(frame)` | none | none | closes the frame and every frame opened after it |
| `check_storage(cost, scope)` | none | `frames_total`, the temporaries and `cost` | none |
| `retained()` | none | none | reads `frames_total` plus the temporaries |

- **Check, then write.** Every operation does its clock reading, charge and
  checks, where it has them, before it writes anything. A rejected frame or frame cost is not charged,
  and the table and `frames_total` stay unchanged. A zero reservation is not
  checked, which cannot be observed from outside, since the retained total
  never exceeds the limits.
- **Reporting.** A storage check compares `max_nodes`, then
  `max_storage_bytes`, and fails with `Field(Nodes)` or
  `Field(StorageBytes)`; when both are exceeded it reports `Nodes`. Sums use
  checked addition, and a `u64` overflow is reported as exceeding that
  component, with the amount marked as a bound.
- **Bounded work.** `check_storage`, `reserve`, `set_frame_cost` and
  `retained` take constant time, whatever the number of open frames.
  `leave_frame` loops at most once per frame that it closes, and each of
  those frames was charged when it was entered.
- **Tokens and generation numbers.** `Frame` and `Reserved` cannot be cloned.
  A `Frame` records the index of its frame and its generation number, a
  `u64` that every `enter_frame` increments. A token whose generation does
  not match is treated as a frame that is no longer open:
  `set_frame_cost` charges 1 unit and writes nothing, and `leave_frame`
  closes nothing. A stale inner token therefore never reaches a frame that
  was opened after its own frame was closed.
- **Exits that do not end the request** return their tokens. A copyable
  `mark()` records the frame count, the generation and the temporaries, and
  `restore(mark)` closes the frames opened since, like `leave_frame`, and
  restores the temporaries; when a method stops with a result state, it
  restores the mark taken on entry. Only a request failure on the `Err` side
  may leave tokens unreturned. `mark` and `restore` arrive with the first
  method that holds tokens and can stop with a state, no later than 0.3.

The library-level checks `check` (for a field) and `check_parameter` (for a
request parameter) are `&self` methods of the context. `check` on `Nodes` is
`check_storage(Storage::new(value, 0), LimitScope::Value)` and on
`StorageBytes` is `check_storage(Storage::new(0, value), LimitScope::Value)`,
so open frames and temporaries count; on the other seven fields it compares a
single value, with no scope.

### Sub-computations and what the context does not hold

- **Sub-computations** in 0.1 charge the same `&mut Context` as their caller,
  in a fixed order. The total work is the sum of the parts and the result is
  deterministic, but which part fails first depends on the order. There is no
  way to allot a budget to a sub-computation and no `remaining_work()`.
  Deterministic sub-budgets that are allotted to parts and settled back are
  planned for 0.7, added on top of the nine fields without changing them;
  until then, sub-computations that share a context never run in parallel,
  and the library starts no threads.
- **Not in the context.** `settings` and `settings_version` are inputs of the
  request, and a progress receiver is a separate parameter of a streaming
  entry ([convention 13](conventions/public-api.md#13-request-inputs-and-progress)).
  Only the command entry and the command-line program construct a `Context`.

## Error kinds

**Status:** implemented in `src/error.rs`; its
[contract](components/errors/contract.md) states the requirements, the place
of every error kind of the earlier implementation and the tests. The rules
below are those of the error component and of every function that returns
its types.

### Error and `Settled<T>`

A request failure is an `Err(Error)`; a mathematical state is
`Ok(Settled::State(..))`. A method without states returns `Result<T>`; a
method with states returns `Result<Settled<T>>`.

```rust
#[non_exhaustive]
#[must_use]
pub enum Settled<T> {
    Value(T),
    State(MathState),
}

#[non_exhaustive]
pub enum MathState {
    NotConverged,
    Unevaluated,
    NotApplicable,
    Undecided,
    IterationLimit,
}
```

All five states exist from 0.1, though no public entry of 0.1 produces one
yet. Inside the library, a method that stops with a state carries it to its
boundary, where it becomes `Settled::State`; there is no conversion from a
state to an `Error`, or back.

### Request failures and faults

`Error` has private fields and the accessors `kind()`, `span()`,
`message()` and `exceeded()`; `exceeded()` is `Some` exactly when the kind is
`ResourceLimit`.

- `ErrorKind` is `ResourceLimit`, `Cancelled`, `DeadlineExceeded` or
  `Fault(FaultKind)`. The first three are request failures, and only the
  context constructs them.
- `FaultKind` has seven foundation kinds in 0.1: `Syntax`, `UnknownSymbol`,
  `DivisionByZero`, `NonIntegerExponent` (the exponent is not an integer
  constant), `NotPolynomial`, `Unsupported` and `Internal`. Features append
  their own kinds in the release that needs them, such as
  `ContradictoryAssumptions`, `InvalidBinding`, `VariableMismatch`,
  `OutsideDomain` and `InvalidInterval` in 0.2, `StaleEnvironment` and
  `DimensionMismatch` in 0.3, and `InvalidMatrix` and `SingularMatrix` in
  0.4.
- Both enums are `#[non_exhaustive]`, and `class()` sorts every kind into
  one of three classes: `Context` for the request failures, `Input` and
  `Internal`.
- `Error::new(kind: FaultKind, span, message)` takes only a `FaultKind`,
  and no public path builds a request failure, so
  `Error::new(ErrorKind::Cancelled, ..)` does not compile; a `compile_fail`
  documentation test with the expected error code checks this.
- `Error` does not derive `PartialEq`, `Eq` or `Hash`, because it carries
  message text. Tests compare `kind()`, `span()` and `exceeded()`, never the
  message.

### Limit identifiers

A `ResourceLimit` error carries a `LimitExceeded { id, scope, allowed,
amount }`, which is `#[non_exhaustive]`, has private fields and no public
constructor, and derives `PartialEq` and `Eq`.

- `id` is a `LimitId`: `Field(LimitField)` for a field of `Limits`, with the
  nine variants `Work`, `InputBytes`, `OutputBytes`, `Depth`, `Nodes`,
  `StorageBytes`, `IntegerBits`, `Exponent` and `Frames`; or
  `Parameter(name)` for an explicit request parameter, with the name as an
  owned string. A bound derived from a field names that field.
- `allowed: u64` is the limit that was in force. A bound set by a machine
  width is written as the field or parameter that dominates it, with
  `allowed` its effective value; a bound that nothing dominates is never a
  `ResourceLimit` ([convention 6](conventions/public-api.md#6-no-hidden-caps)).
- `amount` is `Used` (the total at the failed check), `Required` (the exact
  amount needed) or `Bound` (a reliable upper estimate beyond `allowed`,
  saturated at `u64::MAX`).
- `scope: Option<LimitScope>` says where a `Nodes` or `StorageBytes` limit
  was hit: `Value` (building or admitting a value through `check_storage`),
  `Frame` (the cost of a frame, through `set_frame_cost`) or `Temporary` (a
  reserved temporary, through `reserve`). `LimitScope` is
  `#[non_exhaustive]`, and the scope is `None` for every other field; the
  frame count is the separate field `Frames`.

### Shared result types

The types that describe how good a result is are defined once for the whole
crate, by their first user, and are only extended afterwards; no domain
defines a synonym. `Completeness` and `Evidence` are planned for 0.2, and
`Guarantee` for 0.3. None of them exists in 0.1.

- All three are `#[non_exhaustive]`. `Guarantee` is `Exact`, `Certified`,
  `Estimated` or `Heuristic`; `Evidence` has at least `Proved`, `Refuted`,
  `NumericEvidence` and `Unknown`.
- Combining results never raises the guarantee; numerical evidence never
  becomes `Proved` or true; an `Unknown` from three-valued equality is never
  promoted.
- An evidence field is either computed or absent. Every public state has at
  least one test that produces it. A state is a value and never stands for a
  request failure.
- A feature may define its own status enum when its states carry data or are
  finer, and states which `MathState` each of them refines.
- Variant names are part of the compatibility contract: they are never
  renamed or reused, and the value encoding gives them fixed codes when it
  first encodes them.

### At the command entry

The command entry maps an outcome to the state of the job that runs it:
`Cancelled` and `DeadlineExceeded` to the terminal states that the contract of
the command entry defines together with krepi, `ResourceLimit` and every
`Fault` to failed, and `Settled::State` to completed, with the state attached.
In 0.1, function-call syntax, the reserved names `pi`, `i` and `undefined`,
an unknown operation and a non-default setting fail with `Unsupported`, and a
missing operand fails with `Syntax`.
