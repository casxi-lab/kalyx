# Architecture

This document lists the components of the kalyx library, the verification
tier that each is to reach and its first production caller, and states the
design rules of four foundations that every later part builds on: the term
representation, the coefficient-field trait, the context and the error
kinds. It also states the design rules of the
[function values](#function-values) and the
[algebraic numbers](#algebraic-numbers), which are planned for release 0.2
and which the extension of the term core in that release follows. The
section [requests and results](#requests-and-results) states the rules of
the same release for the extension of the input grammar, the operands of a
request, its results with their output lines, and the table of value kinds.
The interface conventions that all public items follow are in
[the public API conventions](conventions/public-api.md).

**Status.** kalyx ships the errors and result states, the shared result
types `Evidence` and `Truth`, the context and limits, the exact numbers with
the coefficient-field trait over $\mathbb{Q}$, the term core, the parser,
the univariate polynomials over $\mathbb{Q}$, the command entry with its
output lines, the command-line program `kalyx` and the repository checks.
The errors and result states, the shared result types `Evidence` and
`Truth`, the context and limits, the exact numbers with the integer kernel,
the two layers of the coefficient-field trait and `Rationals`, the term core
with its canonical forms, the parser of the [input syntax](semantics.md), the
univariate polynomials with expansion and differentiation, the
crate-internal function registry with the records of the eleven functions of
function expressions and the command entry with the
[output lines](semantics.md#output-lines) are implemented, each with its
contract ([errors](components/errors/contract.md),
[shared result types](components/shared-results/contract.md),
[context](components/context/contract.md),
[numbers](components/numbers/contract.md),
[terms](components/terms/contract.md),
[syntax](components/syntax/contract.md),
[polynomials](components/polynomials/contract.md),
[function registry](components/registry/contract.md),
[command entry](components/command/contract.md), co-signed with
krepi); no other library component below is implemented
yet. For the other components, the tables are
the plan and the design rules are the rules that their code follows when it
lands; each component also gets its own `contract.md` with its requirements
at that time. Where a rule is already enforced by `cargo xtask check`, the
text says so.

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
land as a public or a crate-internal interface with contract tests. The
exceptions are listed here:

- **The function registry fixes all its slots at once.** Its record schema
  holds every slot of the eleven functions from release 0.2 on, also the
  slots that no part of 0.2 reads; those are empty and listed in the
  exemption list of its
  [contract](components/registry/contract.md#exemption-list), each with the
  release that is to fill it.

### Release 0.1

| Component | Tier | A3 upgrade | First production caller |
| --- | --- | --- | --- |
| Repository checks and guard (available today) | A0 | none | not applicable: they check the repository |
| Answer vectors taken from the earlier implementation | A0 | none | not applicable: test infrastructure |
| Errors and result states (`Error`, `Settled<T>`; implemented, [contract](components/errors/contract.md)) | A1 | 0.2, for the result-state core | the context, in 0.1 |
| Context and limits (`Context`, `Limits`; implemented, [contract](components/context/contract.md)) | A1 | 0.2, for the charging core; the frame table first needs proof models of `Vec` and `Box` | exact numbers and the coefficient-field trait over $\mathbb{Q}$, then the term core, the parser and the command entry, in 0.1 |
| Exact numbers and the coefficient-field trait over $\mathbb{Q}$ (`number`, `coefficient`; implemented, [contract](components/numbers/contract.md)) | A0; the coefficient-field interface is planned for A2 in 0.2 | none | the term core and the polynomials over $\mathbb{Q}$, in 0.1 |
| Term core and canonical forms (`term`; implemented, [contract](components/terms/contract.md)) | A1; canonical forms are planned for A2 in 0.2 | none | the parser and the command entry, in 0.1 |
| Parser (`syntax`; implemented, [contract](components/syntax/contract.md), grammar in [the input syntax](semantics.md)) | A1 | none | the command entry, in 0.1 |
| Univariate polynomials over $\mathbb{Q}$ with expansion and differentiation (`polynomial`; implemented, [contract](components/polynomials/contract.md)) | A0; planned for A2 in 0.2 | none | the command entry (`expand`, `diff`), in 0.1 |
| Command entry and output serialization (`command`; implemented, [contract](components/command/contract.md)) | A1 | none | the command-line program, in 0.1; the calculator job of krepi, built from a pinned 0.1 commit |
| Command-line program (`src/main.rs`; implemented, forms in [the command-line program](semantics.md#the-command-line-program)) | A0 | none | none: it is the top level |

### Later foundations

These foundations are planned for later releases. Their tiers are filled in
when each release is planned, except where the plan already fixes them.

| Component | Release | Planned tiers | First production caller |
| --- | --- | --- | --- |
| Term core extension: constants, function-call nodes, conditions and assumptions | 0.2 | A2 for canonical forms | the function-expression baseline (elementary functions, $\pi$, $i$, conditions and `piecewise`), 0.2 |
| Integer kernel: the arithmetic of `Integer`, GCD, LCM, extended GCD, modular inverse, modular power and Chinese remaindering (`number`; implemented, [contract](components/numbers/contract.md#the-integer-kernel)) | 0.2 | A1; Chinese remaindering is planned for A2 in 0.4, with the fast arithmetic; no A3 upgrade | the GCD and the factorization of polynomials over $\mathbb{Q}$, 0.2 |
| Coefficient-field interface and fields beyond $\mathbb{Q}[x]$: $\mathbb F_p$ (`PrimeField` in `coefficient`; implemented, [contract](components/numbers/contract.md#prime-fields)), $\mathbb{Z}$, $\mathbb{Q}(a)$, multivariate rings, monomial orders, homomorphisms | 0.2 | A2 for the interface; A1 for $\mathbb F_p$; A3 upgrades in 0.2 for prime fields and monomial orders | $\mathbb F_p$: the multimodular GCD over $\mathbb{Q}$ and the Berlekamp factorization, 0.2; the others: real root isolation and algebraic numbers, and basic polynomial algorithms over $\mathbb{Q}$, 0.2 |
| Elimination skeleton: Gauss–Jordan elimination over a coefficient field | 0.2 | set when planned | basic polynomial algorithms over $\mathbb{Q}$, 0.2 |
| Function registry: the records of the eleven functions of function expressions and the identity list (`registry`, crate-internal; implemented, [contract](components/registry/contract.md)) | 0.2 | A1; A3 upgrade in 0.3 | the function-expression baseline, with the derivatives and the Taylor series of function expressions, 0.2; the call constructor of the term core reads the records in the same release and is not counted as the first caller |
| Shared result types: `Evidence` and `Truth` (implemented, [contract](components/shared-results/contract.md)), `Completeness`; then `Guarantee` | 0.2; `Guarantee` in 0.3 | A1; no A3 upgrade; the tier of `Guarantee` is set when 0.3 is planned | the assumption queries of function expressions (`Evidence`, `Truth`; the assumption system of the same release answers them through these types and is not counted), root lists and real sets (`Completeness`), zero tests of algebraic numbers (`Evidence`), 0.2; numerical evaluation (`Guarantee`), 0.3 |
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

**Status:** implemented in `src/term.rs` for numbers, symbols, powers,
products and sums; its [contract](components/terms/contract.md) writes the
rules of these kinds out as invariants, with the display grammar, the charges
and the tests. The constants, the rules of calls and the conditions are
planned for release 0.2 and not implemented: no constructor builds a
constant, a call or a condition yet. The subsections
[constants](#constants), [rules of the call constructor](#rules-of-the-call-constructor)
and [conditions](#conditions), and the parts of the other subsections that
are marked as planned, state the design rules that their code follows when
it lands; the contract writes them out then.

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

Comparison, display and the collection of negative-exponent bases are each a
loop over a stack on the heap, and the constructors keep their work lists on
the heap; none recurses natively. Their frames hold owned terms (a clone only
increments a count) and copied scalars, never borrowed references. `Drop` for
a node moves its children onto a stack of its own and releases them one at a
time with `Rc::try_unwrap`, so dropping a deep term uses a constant amount of
native stack. The native stack use of term operations therefore does not grow
with the depth of the term; the [resource profile](resource-profile.md)
measures the stack and the heap of requests on one host.

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
| Condition (reserved for conditions) | 7 |

A new kind takes a new rank and never changes the relative order of the
existing kinds. Ranks 0 to 6 are the value classes and rank 7 is the kind of
the [conditions](#conditions), and values and conditions are kept apart
(planned): a condition is never an operand of a sum, a product, a power or a
value argument of a call. Terms are totally ordered by rank first. Within a
rank:

- numbers by value;
- constants (planned): the named constants first, by the bytes of their
  names, so $i$ comes before $\pi$, then the algebraic constants, in the
  structural order of [their identities](#order-and-cache);
- symbols by their UTF-8 bytes;
- calls by the bytes of the head name, the head class, the arguments one by
  one, and the number of arguments;
- powers by base, then exponent;
- products by their factors one by one, the number of factors, then the
  coefficient;
- sums by their monomials one by one (core, then coefficient), the number of
  monomials, then the constant;
- conditions (planned): by shape first, then by the relation or the
  property, then by their subterms one by one, then by the number of
  subterms.

Comparison is structural, and each step is charged. It takes the children
of two nodes one pair at a time, so every step does a bounded amount of work,
and the pairs after the first one that differs are never visited.

### Canonical forms

The constructors keep every term in canonical form:

- **Products.** Nested products are flattened, and numeric coefficients are
  multiplied exactly. A sum among the factors is taken by its primitive
  part, as stated below: its content joins the coefficient, so
  $(2x + 2y) z = 2 (x + y) z$. Factors with the same base and the same sign
  of exponent are merged by adding exponents, so
  $(2x + 2y)(x + y) = 2 (x + y)^2$; factors with exponents of opposite sign
  are not merged, except over a [constant](#constants) base, which is
  planned. Factors are sorted, and a product contains no number and
  no product as a factor. A product with coefficient 1 and a single factor
  is that factor, and a coefficient other than 0 and 1 times a single sum
  is that sum scaled by the coefficient.
- **Powers.** The exponent is an integer. A numeric base is evaluated
  strictly, and the exponent limit is checked before the value is computed.
  An exponent of 1 returns the base. An integer power distributes over a
  product, $(c \prod f)^k = c^k \prod f^k$. A power of a sum $s = c \cdot p$,
  with its content $c$ and its primitive part $p$, is $c^k p^k$ with $c^k$
  evaluated strictly: $(2x + 2y)^2 = 4 (x + y)^2$ and
  $(1 - x)^{-1} = -(x - 1)^{-1}$. A power of a power $(b^j)^k$ becomes
  $b^{jk}$ only when $jk \lt 0$, when $j, k \ge 0$, or when $j = 0$. A power
  of a sum is not expanded.
- **Sums.** Nested sums are flattened, and monomials with the same core add
  their coefficients. A numeric coefficient $c$ other than 0 and 1 times a
  sum $s$ is the sum whose constant and coefficients are those of $s$
  multiplied by $c$, so $2(x + y) = 2x + 2y$ and $-(x + y) = -x - y$, and no
  monomial core of a sum is a sum; the coefficient 0 follows the witnesses
  below.
- **Primitive parts.** The content $c$ of a sum $s$ is the coefficient of its
  first monomial, in the term order, whose coefficient is not 0, or its
  constant when its only monomial is a witness; it is never 0. The primitive
  part of $s$ is $p = s / c$, whose content is 1, so
  $(3x + 2y) z = 3 (x + \frac{2}{3} y) z$. It takes only the division of
  rationals, never a greatest common divisor. A sum that is a factor of a
  product or the base of a power is always taken by its primitive part.

The canonical form does not depend on the order in which a term was built:
under associativity and commutativity the result is the same, and rebuilding
a canonical term gives a structurally equal term. So scaled copies of one sum
merge in every grouping: with $s = x + y$, $a = 2s$ and $b = -s$, the sums
$a + b + b$ and $(a + b) + b$ are both 0, $(a + b) + (a + b)$ and
$a + b + a + b$ are both $2x + 2y$, and $s - s = 0$.

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

A branch of `piecewise` that a decided condition discards is never built,
so it cannot fail ([branches](#branches), planned); every subterm that is
built is evaluated strictly.

### Negative-exponent invariant

Write $N(t)$ for the set of bases that occur with a negative exponent in a
term $t$, and $\max N(t)$ for those elements of $N(t)$ that do not themselves
occur with a negative exponent inside another element. A base that is a sum
is taken by its primitive part, also inside the witnesses below: a power of
a sum $s = c \cdot p$ raises $p$, and since $c \ne 0$, $s$ and $p$ are 0 at
the same points. A [constant](#constants) (planned) is never 0 and, like a
number, never an element of $N(t)$. Canonicalization never shrinks this
set:

```math
N(\mathrm{input}) \subseteq N(\mathrm{output})
```

The invariant is stated for the value classes, ranks 0 to 6. A
[condition](#conditions) (planned) can lose a base by absorption, as
$\mathrm{false} \land (1/x \gt 0) = \mathrm{false}$ loses $x$, but only where
the condition has a value.

The negative power that `power` and `divide` introduce is kept as well: the
result is undefined wherever the base or the divisor is 0, unless the
construction fails with `DivisionByZero`. A canonical form therefore never
hides a point where its input is undefined. With calls (planned), this holds
because a call is a total uninterpreted atom of the term core, and the
partiality of a function is carried by the condition of a
[function value](#domains-of-calls), not by the term: as terms,
$0 \cdot \log x$ and $\log x - \log x$ are 0 and $(\log x)^0$ is 1, and the
function value of each keeps the condition $x \ne 0$. Where a simplification
would lose a base, the term keeps a witness instead:

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
$(x^{-1})^0$ each stay as written, while $x^{-1} x^{-2} = x^{-3}$ and
$0 \cdot (2x + 2y)^{-1} = 0 \cdot (x + y)^{-1}$. Removing negative exponents
under conditions is an explicit operation of the
[function values](#removing-negative-exponents), never part of a
constructor.

### Constants

**Status:** planned for release 0.2; no constant exists yet, and `pi` and
`i` are [reserved names](#reserved-names).

Rank 1 holds the named constants $\pi$ and $i$ and the
[algebraic constants](#algebraic-numbers-as-terms). The named constants are
a crate-internal `#[non_exhaustive]` enumeration, ordered by name and not by
variant, so adding a constant changes no existing order. Every constant is
an exact number other than 0, and the term core uses this:

- **Not a base of $N$.** A constant never enters $N(t)$, so a power of a
  constant leaves no witness: $c^0 = 1$ and $0 \cdot c^{-1} = 0$ for a
  constant $c$. A term whose negative powers all have constant bases, such
  as $\pi^{-1}$, has an empty $N$.
- **Exponents of both signs merge.** Factors with the same constant base add
  their exponents whatever their signs, so $\pi \cdot \pi^{-1} = 1$.
- **Powers of $i$.** $i^k$ is $1$, $i$, $-1$ or $(-1) \cdot i$ by
  $k \bmod 4$, for every integer $k$, and the result returns to the merging
  worklist, so $i \cdot i = -1$ and $i^{-3} = i$. A power of $\pi$ or of an
  algebraic constant is not reduced.
- **Why only constants.** The reduction of the powers of a constant is
  defined for every integer exponent and agrees with the addition of
  exponents: it is a homomorphism from $\mathbb{Z}$, which keeps the
  canonical form of a product independent of its grouping when exponents of
  both signs merge. A call is never such a base, also when its arguments are
  rational: $\sqrt{2}$ is a call, its powers follow the rule of root powers
  only for positive exponents, and $\sqrt{2}^{-1}$ keeps $\sqrt{2}$ in $N$.
- **Algebraic constants are atoms.** For the call constructor an algebraic
  constant is an opaque atom other than 0, and no constructor folds
  arithmetic between algebraic constants into one constant: for an algebraic
  constant $c$ of degree 3, $c^3$ stays $c^3$.

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

The two classes of calls are planned as follows. The functions of the
function registry, such as `sin`, `log`, `sqrt` and `rootn`, are calls of the
class `Registered`, and the rules of the registry apply to these calls only.
The three special forms `piecewise`, `derivative` and `substitute` are calls
of the class `Formal`, with reserved head names and a variable number of
arguments; a table of the special forms states the role of each argument,
and the registry holds no record for them:

- `piecewise(c, a, b)` takes a [condition](#conditions) $c$ and two values,
  as the [function values](#branches) state;
- `derivative(u, x, n)` takes an order $n$ between 1 and `max_exponent`, and
  `derivative(u, x, 0)` is $u$;
- `substitute(u, x1 = v1, …)` keeps its bindings sorted by name, and a name
  bound twice fails with `InvalidBinding`.

The call constructor simplifies neither `derivative` nor `substitute`. The
free symbols of a term and substitution skip the variable and binding
positions that the table of special forms names, so substituting $x := 2$
does not enter $u$ in `derivative(u, x, n)`.

### Rules of the call constructor

**Status:** planned for release 0.2; the
[function registry](components/registry/contract.md) that it reads is
implemented, and no constructor builds a call yet. The contract of the term core fixes the rules
below once, with their charges.

A rule $L \to R$ is eligible for the call constructor, or for the term core
with a call head or a constant as its trigger, exactly when

```math
[L]\rho = [R]\rho \quad \text{for every assignment } \rho
```

with values in $\mathbb{C} \cup \lbrace \bot \rbrace$, where $\bot$ marks an
undefined value: both sides have the same domain, and the rule needs no
assumption. A rule that holds only under an assumption, or whose left side
is defined at fewer points than its right side, belongs to the scoped
rewriting of function expressions, the planned command `f-refine`, which
keeps the domain of the left side as a condition. An eligible rule keeps
the meaning of the term it rewrites, so it never widens a domain, which
would hide a point where its input is undefined. The rules of sums,
products and powers treat a call as a total atom, and the function value
carries the domain of the call ([domains of calls](#domains-of-calls)).
Not every eligible rule is applied: the rules are placed as follows, and
the last item of the list after the table names rewritings that the
constructors of release 0.2 do not apply.

| Rule | Where it applies |
| --- | --- |
| A name that the registry does not hold, and a wrong number of arguments, fail with `Syntax`; the number of arguments is checked before any domain | call constructor |
| The degree $n$ of `rootn(u, n)`: a literal positive integer is accepted; 0, a negative integer, a rational that is not an integer, $\pi$ and $i$ fail with `OutsideDomain`, and a degree beyond `max_exponent` fails with `ResourceLimit`; any other degree, such as a symbol or a sum, builds the call and leaves "$n$ is a positive integer" to the condition of the function value | call constructor |
| An argument `undefined` fails with `OutsideDomain` | call constructor |
| $\mathrm{rootn}(u, 2) = \sqrt{u}$ and $\mathrm{rootn}(u, 1) = u$, for a literal degree | call constructor |
| The domain fails with `OutsideDomain` on these arguments only: $\log 0$; $\tan(q\pi)$ with $2q$ an odd integer; `asin` and `acos` on a rational $q$ with $\lvert q \rvert \gt 1$; `asin`, `acos` and `atan` on $c \cdot i$ with a rational $c \ne 0$. A zero witness counts as 0 here, as it does for division, so $\log(0 \cdot x^{-1})$ fails. On any other argument, such as `asin` on $q\pi$, the call is built and its domain goes into the condition of the function value | call constructor |
| Parity: `sin`, `tan`, `asin` and `atan` are odd and `cos` and `abs` are even, and `acos` is reflected, $\arccos(-u) = \pi - \arccos u$. They apply when the argument $u$ is a negative number, a product with a negative coefficient or a sum whose content is negative: $f(u)$ becomes $-f(-u)$ for an odd $f$, $f(-u)$ for an even $f$, and $\arccos u$ becomes $\pi - \arccos(-u)$ | call constructor |
| Point values: $\sin 0 = \tan 0 = 0$, $\cos 0 = \exp 0 = 1$, $\log 1 = 0$, $\sqrt{0} = 0$, $\sqrt{1} = 1$, $\mathrm{rootn}(0, n) = 0$ and $\mathrm{rootn}(1, n) = 1$ for a literal $n$, `asin`, `acos` and `atan` at $-1$, 0 and 1, and $\lvert i \rvert = 1$ | call constructor |
| Quarter turns: `sin`, `cos` and `tan` at $q\pi$ with $2q$ an integer, where `tan` at an odd multiple of $\pi/2$ fails as above | call constructor |
| Principal roots of rationals, normalized as [their section](#principal-roots-of-rationals) states | call constructor |
| Absolute values: $\lvert q \rvert$, $\lvert c\pi \rvert = \lvert c \rvert \pi$ and $\lvert c i \rvert = \lvert c \rvert$ for rationals $q$ and $c$, and $\lvert \lvert u \rvert \rvert = \lvert u \rvert$ | call constructor |
| Powers of roots: for a literal degree $n$ and every $k \ge 1$, $(\sqrt[n]{u})^k = u^{\lfloor k/n \rfloor} (\sqrt[n]{u})^{k \bmod n}$, read from the registry, with the factors returning to the same worklist; a negative $k$ leaves the power as it is | term core, with the head names `sqrt` and `rootn` as trigger |
| Powers of $i$: $i^k = i^{k \bmod 4}$ for every integer $k$, as stated for [constants](#constants) | term core, with the constant $i$ as trigger |
| $\mathrm{piecewise}(\mathrm{true}, a, b) = a$ and $\mathrm{piecewise}(\mathrm{false}, a, b) = b$ | term core, with the head name `piecewise` as trigger |
| Periodicity, also by literal multiples: `sin` and `cos` drop $2k\pi$, `tan` drops $k\pi$ and `exp` drops $2k\pi i$ from their argument | `f-refine`; a literal $k$ needs no assumption, a symbolic $k$ needs $k \in \mathbb{Z}$ |
| Rules that need an assumption: $\sqrt{u^2} = \lvert u \rvert$ for a real $u$, $\log(\exp u) = u$ for $-\pi \lt \mathrm{Im}(u) \le \pi$, and the sign rules of `abs` | `f-refine` |
| Rules whose left side has a smaller domain: $\exp(\log u) = u$, $\sin(\arcsin u) = u$, $\cos(\arccos u) = u$ and $\tan(\arctan u) = u$ | `f-refine`, which keeps the domain of the left side |
| The instances of these rules on exact constants, such as $\exp(\log 2) = 2$ and $\sqrt{\pi^2} = \pi$ | `f-refine`, which decides them in the empty scope |
| Merging equal branches, $\mathrm{piecewise}(c, a, a) = a$, and removing negative exponents under conditions | [function values](#function-values) |

- **Registered calls only.** No rule of the registry applies to a formal
  call; the three rules of the term core are triggered by a head name or a
  constant, not looked up in the registry, except that the powers of roots
  read their identity from it.
- **Shapes, not properties.** The value tables, the point values, quarter
  turns, principal roots and absolute values, match only the shape of the
  argument: a number, $\pi$, $i$, or a rational multiple of $\pi$ or $i$. A
  zero witness matches none of them, since $\cos(0 \cdot x^{-1}) = 1$ would
  lose $x$ from $N$, so $\cos(x^{-1} - x^{-1})$ stays
  $\cos(0 \cdot x^{-1})$. The rules on the degree of `rootn` apply only to a
  literal degree, so $\mathrm{rootn}(0, n)$ stays as it is for a symbol $n$.
  The call constructor infers no property of its arguments:
  $\lvert \sqrt{2} \rvert$ stays as it is, and every rule that needs a
  property is in `f-refine`.
- **Order of the rules.** In one call the constructor checks the number of
  arguments, then the degree, applies the two rules of `rootn`, checks the
  domain, applies parity, then the value tables, then
  $\lvert \lvert u \rvert \rvert = \lvert u \rvert$. The rules terminate and
  give the same result in every order, so the order fixes only the charges.
- **Examples.** $\sin(x - y) + \sin(y - x) = 0$, and $\sin(1 - x)$ is
  $-\sin(-1 + x)$. With $s = \sqrt{x}$, the products $s \cdot s \cdot s \cdot s$
  and $(s \cdot s) \cdot (s \cdot s)$ are both $x^2$, and
  $\mathrm{rootn}(x, 3)^6 = x^2$, while $\sqrt{x}^{-2}$ stays as it is.
  $\lvert -\lvert x \rvert \rvert = \lvert x \rvert$. $\cos(x + 2\pi)$ stays
  as it is until `f-refine` rewrites it. $\arcsin \pi$ builds a call, and its
  function value fails with `OutsideDomain`.
- **Not in the constructors of release 0.2.**
  $\exp a \cdot \exp b = \exp(a + b)$; special values
  beyond the tables, such as $\sin(\pi/6)$ and $\log(-1) = \pi i$;
  $\mathrm{rootn}(\mathrm{rootn}(u, m), n) = \mathrm{rootn}(u, mn)$;
  $\lvert c u \rvert = \lvert c \rvert \lvert u \rvert$ and
  $\sqrt{c u} = \sqrt{c}\sqrt{u}$ for a rational $c \gt 0$;
  $\sqrt{u}\sqrt{v} = \sqrt{uv}$; extraction from radicals, such as
  $\sqrt{8} = 2\sqrt{2}$; general powers $u^v$; $\arcsin(\sin u) = u$ and the
  other inverse compositions; arithmetic between algebraic constants; and
  $0 \cdot \mathrm{piecewise}(c, a, b) = \mathrm{piecewise}(c, 0 \cdot a, 0 \cdot b)$.

### Function knowledge

Function knowledge lives only in the function registry. What the library
knows about one of the eleven registered functions, such as its domain, its
cut, its special values and symmetries, its derivative and its series, is a
slot of its record, and what relates calls of several of them, or nested
calls, is an entry of the identity list of the registry, as its
[contract](components/registry/contract.md) states; the registry is
implemented. Its readers are planned for release 0.2: the call table of the
parser, the call constructor, the builder of function values, the scoped
rewriting `f-refine`, differentiation, the series of function expressions
and the assumption system are to read the records and the entries, and none
of them is to keep a table or a rule of a registered function of its own,
so a function added later brings its knowledge as a record. The rules of
the term core that a head name or a constant triggers are no knowledge of a
registered function, as the rule on registered calls above states; the
powers of roots are to read their identity, the entry `root_pow`, from the
registry.

### Conditions

**Status:** planned for release 0.2; no condition exists yet.

A condition is a term of rank 7. At each assignment of its symbols it is
true, false or undefined. Its shapes are the truth values `true` and
`false`, comparisons of values, property predicates of a value,
`defined(u)`, which states that $u$ is defined, and the connectives `not`,
`and` and `or`; the set of shapes is `#[non_exhaustive]`.

- **Two classes.** The operands of the connectives and the first argument of
  `piecewise` are conditions; every other operand and argument is a value.
  An operand of the wrong class fails with `Fault(Syntax)`.
- **Strict atoms.** The domain of a comparison or a property predicate is
  the intersection of the domains of its operands, and an ordered comparison
  also needs real operands: it is undefined where an operand is not real.
- **Strong Kleene connectives.** An `and` with a false operand is false and
  an `or` with a true operand is true, whatever the other operands are,
  undefined included. Otherwise a connective with an undefined operand is
  undefined, and so is `not` of an undefined operand; on defined operands
  the connectives are the Boolean ones. So `and` and `or` are commutative,
  associative and idempotent on the three values, and
  $x = 0 \lor 1/x \gt 1$ is true at $x = 0$.
- **Structural normalization only.** The constructor of conditions flattens
  nested `and` and `or`, sorts their operands and removes repeated ones,
  rewrites $\lnot\lnot c$ to $c$, and absorbs `true` and `false`. Under the
  strong Kleene connectives each of these is an identity on the three
  values, so it meets the criterion of the
  [call constructor](#rules-of-the-call-constructor), and the domain of an
  absorbed operand needs no record. The term core decides no comparison;
  deciding one belongs to the function expressions.
- **Spelling.** The input writes a condition as `true` or `false`; as a
  comparison of two values with one of the relations `==`, `!=`, `<`, `<=`,
  `>` and `>=`; as a predicate `is_<property>(u)` or `defined(u)`; or as a
  connective in call form, `not(c)` with one condition and `and(c, c, …)`
  and `or(c, c, …)` with two or more. A comparison has one relation and is
  not associative, so `0 < x < 1` fails with `Syntax`. There are no infix
  connectives and no conditions in parentheses. The operands of a
  comparison and the argument of a predicate are value positions, and the
  property names are those of the list of the assumption system. The
  example of the strong Kleene connectives above is written
  `piecewise(or(x == 0, 1/x > 1), 1, 2)`.
- **A start symbol of its own.** A condition operand is read by a start
  symbol of its own, `condition_input`: the condition operands of the
  planned commands `ineq`, `rel-and`, `rel-or` and `rel-not` use it, and so
  does the condition column of an [answer line](#answers-and-output-lines)
  when it is read back. The first argument of `piecewise` and the operands
  of the connectives are read by the same production.
- **Reading the start of a condition.** Two tokens decide the production,
  by the same rule as in a value position, where only a name followed by
  `(` is a call:
  1. `true` and `false` are the truth values, which take precedence over a
     symbol as reserved keywords, and no relation may follow them:
     `true == x` fails with `Syntax`, while `x == true` compares the
     symbol `true`.
  2. An identifier followed by `(` is looked up among the condition heads:
     `not`, `and` and `or` are connectives, and `defined` and the names
     that start with `is_` are predicates; `is_` followed by a name outside
     the list of properties fails with `Syntax`, with the span of the name.
     A head of a value position starts a comparison, as in `sin(x) > 0`,
     and any other head is unknown and fails with `Syntax`, as in a value
     position. The condition heads and the heads of value positions are
     disjoint.
  3. Any other token starts a comparison. An identifier that `(` does not
     follow is a symbol, `not`, `defined` and `is_foo` included, so
     `is_foo == 1` compares the symbol `is_foo`.

  A condition head that a later change adds, such as a new property or a
  new predicate, turns only a `name(` that failed with `Syntax` into a
  condition, so every accepted condition keeps its meaning. In 0.2,
  `stable(…)` is no condition and fails as an unknown head.
- **Display.** A relation has one space on each side, as in `x != 0`, and
  the connectives are written in call form, in the order that the
  normalization above gives. When the first token of the displayed left
  side of a comparison is `true` or `false`, the whole left side is in
  parentheses, as in `(true) == x` and `(true + x) == y`, so the display of
  a condition always reads back. The other condition heads need no
  parentheses, since the display of a value never has one followed by `(`.

### Reserved names

`pi` and `i` are reserved for the constants $\pi$ and $i$, and `undefined`
for the branch of a `piecewise` that has no value. In 0.1 the parser and
`Term::symbol` reject all three with `Unsupported`, as they reject
function-call syntax. An input accepted by 0.1 therefore keeps its meaning
and its canonical form when the constants arrive; otherwise $i \cdot i$
would change from $i^2$ to $-1$, and the rank of `pi` from 2 to 1. Later
constant names are taken only from the reserved names or from spellings that
are errors in 0.1.

As planned, `undefined` is neither a constant nor a term, and it has no
rank. It is accepted only as a branch of `piecewise`, and building the
function value [removes it](#branches), so the condition is the one record of
where a function value is undefined, and the term core needs no rule for a
value that is not a number. On its own, as an argument of any other call, as
an operand, or where removing it leaves a false condition, it fails with
`OutsideDomain`. The head names `piecewise`, `derivative` and `substitute`
are reserved for the special forms of the [call nodes](#call-nodes).

**Words by position** (planned). An identifier that is valid in 0.1 is a
symbol in every value position, in 0.2 and in every later release. A word
takes a new meaning only where 0.1 fails: where `(` follows it, under a new
[start symbol](#one-grammar-read-by-role), or in an argument position of a
special form. By position, the words read as follows:

| Word | Value position | Followed by `(` | Condition position | Binding name, variable position |
| --- | --- | --- | --- | --- |
| `pi`, `i` | the constant | `Syntax` | in an operand, the constant | a binding name fails with `InvalidBinding`; a variable position fails with `Unsupported`, as in 0.1 |
| `undefined` | only a whole branch of `piecewise`; elsewhere `OutsideDomain` | `Syntax` | — | as for `pi` and `i` |
| the names of the eleven registered functions, such as `sin` and `rootn`; `piecewise`, `derivative` and `substitute`; `root` and `croot` | a symbol | a call, a special form or a literal | as in a value position | an ordinary name |
| `true`, `false` | a symbol | `Syntax` | at the start of a condition, the truth value, which takes precedence over a symbol as a reserved keyword; in an operand of a comparison, a symbol | an ordinary name |
| `and`, `or`, `not`, `defined`, `is_<name>` | a symbol | in a value position, `Syntax`, as an unknown head | followed by `(`, a connective or a predicate, where `is_` followed by a name outside the list of properties fails with `Syntax`; otherwise a symbol | an ordinary name |
| `field`, `field_element`, the interval heads, `union`, `reals` | a symbol | a head only under its own start symbol | — | an ordinary name |
| `a` | a symbol | — | — | an ordinary name |
| `e`, `E`, `I`, `Pi`, `inf`, `empty` | a symbol, and never a constant in a later release | — | — | an ordinary name |

So `pi(2)` fails with `Syntax`; `(undefined)` as a branch is `undefined`,
and `-undefined` fails with `OutsideDomain`; $i\pi$ and $2i$ display as
`i*pi` and `2*i` and read back as the same terms; and `Pi`, `I` and
`undefined_` stay symbols. In an element position of a
[number field](#extensions-of-the-grammar), `a` is the generator. How a
condition decides between its heads and a symbol is stated in
[conditions](#conditions).

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
- Every step is charged, including the scans of monomials and the
  collection loops, which are charged per monomial they pass. There is no
  hidden cap, and a broken internal invariant returns an `Internal` error.

## Function values

**Status:** planned for release 0.2, with the function-expression baseline;
not implemented. The commands named here, `fexpr`, `f-refine`, `ask`,
`f-ask` and `at`, are planned commands of that baseline and do not exist
yet.

The term core keeps no domain and no assumption. A function value adds
them: it is a triple $(t, C, S)$ of a term $t$, a [condition](#conditions)
$C$ and a scope $S$, an explicit value that holds assumptions about names.

### Meaning of a function value

- **Terms and conditions.** The meaning $[t]$ of a term is a strict partial
  function of the assignments of its symbols to complex numbers: a node is
  defined where its children are defined and lie in the domain of its
  operation. A condition $c$ is true, false or undefined at each assignment,
  and $D_c$ is the set of assignments where it is defined.
- **Function values.** At an assignment that satisfies $S$, the value
  $(t, C, S)$ is $[t]$ where $C$ is true and $[t]$ is defined, and undefined
  elsewhere. At an assignment that does not satisfy $S$, it asserts nothing.
- **The scope is the premise of the assertion.** Building a function value
  (`fexpr`), the term constructors and the decision of conditions never read
  the scope; only the scoped rewriting `f-refine` and the assumption queries
  `ask` and `f-ask` read it. So with the scope "$x$ is positive", the
  function value of $\sqrt{x^2}$ keeps $\sqrt{x^2}$, and `f-refine` rewrites
  it to $x$.
- **Substitution.** Write the scope of a value as $S' \land (x : M)$, where
  $M$ holds its facts about $x$. Substituting the value $(t_u, C_u, S_u)$ for
  $x$ turns these facts into a condition $F_M(t_u)$ on the substituted term:

  ```math
  \bigl( t[x := t_u],\ C[x := t_u] \land C_u \land F_M(t_u),\ S' \land S_u \bigr)
  ```

  An operation on two values joins their scopes by intersecting their facts
  about each name, and fails with `ContradictoryAssumptions` when an
  intersection is empty. The facts about a name are a set of classes that
  partition the complex numbers, and every property is a union of classes,
  so a query about one name is exact; the assumption system fixes the
  classes and the properties.

### Domains of calls

The builder of function values works bottom-up and gives each subterm $u$ a
condition $C_u$. At a [strict position](#removing-negative-exponents) the
conditions of the children are conjoined.

- When the builder builds a call of `tan`, `asin`, `acos`, `atan`, `log` or
  `rootn`, it adds the domain of the call to the condition; the functions
  defined on all their arguments add nothing. A call of `derivative` or
  `substitute` adds `defined(…)` of itself.
- The term core treats every call as a total uninterpreted atom
  ([negative exponents](#negative-exponent-invariant)), so the condition is
  the one record of the domains of calls. A term built with the term
  constructors alone can hide the points where its calls are undefined, and
  the contract of the term core is to state this when calls land.

### Branches

The meaning of $\mathrm{piecewise}(c, a, b)$ is $[a]$ where $c$ is true,
$[b]$ where $c$ is false, and undefined where $c$ is undefined, so its domain
is

```math
D_{\mathrm{piecewise}(c, a, b)} = D_c \cap \bigl( (c \cap D_a) \cup (\lnot c \cap D_b) \bigr)
```

and the builder gives it the condition

```math
C_c \land \bigl( (c \land C_a) \lor (\lnot c \land C_b) \bigr)
```

which states this domain exactly, because a false operand makes a conjunction
false under the strong Kleene connectives, whatever the other operand is.
So $\mathrm{piecewise}(x \ne 0, \log(\log x), 0)$ is 0 at $x = 0$ and
undefined at $x = 1$.

- **Equal branches.** $\mathrm{piecewise}(c, a, a)$ is $a$, and the builder
  keeps $D_c$ in the condition: $\mathrm{piecewise}(1/x \gt 0, 1, 1)$ is 1
  with a condition that still requires $x \ne 0$.
- **The branch `undefined`.** $\mathrm{piecewise}(c, a, \mathrm{undefined})$
  is $a$ with $c$ added to the condition, and
  $\mathrm{piecewise}(c, \mathrm{undefined}, b)$ is $b$ with $\lnot c$, with
  the same value and the same domain. Where `undefined` occurs anywhere else,
  or where the condition is false after the removal, the builder fails with
  `OutsideDomain`.
- **Lazy branches.** The builder builds the condition first. When it is
  `true` or `false`, the other branch is parsed but never built, so
  $\mathrm{piecewise}(\mathrm{true}, 7, 1/0)$ is 7, while $1/0$ alone fails
  with `DivisionByZero`. When it is undecided, both branches are built
  strictly, so $\mathrm{piecewise}(x \gt 0, \log 0, 3)$ fails with
  `OutsideDomain`. Substitution, `at` and `f-refine` decide the condition
  first as well when they rebuild a `piecewise`. Every term that is built is
  evaluated [strictly](#strict-numeric-evaluation).
- **A known limit.** The zero product keeps the bases of negative powers
  inside the branches: $0 \cdot \mathrm{piecewise}(x = 0, 1, 1/x)$ is
  $0 \cdot x^{-1}$, which fails at $x = 0$, where the input has the value 0.
  Such an input fails; it never gives a wrong value.

### Removing negative exponents

A strict position of a term is a position that is reached from the root
without passing into a branch of `piecewise` or into an argument of
`derivative` or `substitute`: the operands of sums, products, powers and
registered calls, the operands of comparisons and predicates, and the
condition of `piecewise`. Where a subterm at a strict position is
undefined, the whole term is undefined.

The operation that removes negative exponents under conditions works on the
strict positions. There it merges the factors with the same base and
exponents of opposite signs and removes the three witnesses, and it adds to
the condition $b \ne 0$ for each base $b$ that it cancels. At a
$\mathrm{piecewise}(c, a, e)$ in a strict position, it works on each branch
separately and joins the conditions $C_a^{\ast}$ and $C_e^{\ast}$ of the two
results as $(c \land C_a^{\ast}) \lor (\lnot c \land C_e^{\ast})$. A call
of `derivative` or `substitute` is an atom. The result has the same domain
and the same value as the input: where a base that occurs with a negative
exponent at a strict position is 0, the input is undefined, and a base that
occurs only in a branch is carried by the condition of that branch.

- $x^2 x^{-1}$ gives $x$ with $x \ne 0$, and $0 \cdot x^{-1}$ gives 0 with
  $x \ne 0$; $1/x$ stays as it is. `at` at $x = 0$ therefore fails with
  `DivisionByZero` on $1/x$ and with `OutsideDomain` on $x^2 x^{-1}$.
- $\mathrm{piecewise}(x = 0, 1, x/x)$ is 1 everywhere, and `at` at $x = 0$
  gives 1.
- The operation has a name in the function expressions and is never part of
  a constructor: it reads terms through the accessors and rebuilds them with
  the public constructors. Every command that builds a function value, such
  as `fexpr`, calls it as its last step, so the function value of $x/x$ is 1
  with the condition $x \ne 0$, and the term of a function value can differ
  from the canonical form of the same input.

## Coefficient-field trait

**Status:** the two traits `CoefficientRing` and `CoefficientField`,
`ZeroTest` and `Rationals` are implemented in
`src/coefficient.rs`, over the exact numbers of `src/number.rs`, and the
prime fields $\mathbb F_p$, `PrimeField` and its elements `PrimeResidue`,
in `src/coefficient/prime.rs`, with the trait implementations in
`src/coefficient/prime/traits.rs`; their
[contract](components/numbers/contract.md) states the checks, the charges and
the tests, those of the prime fields in its section
[Prime fields](components/numbers/contract.md#prime-fields).
`PolynomialRing` and `Polynomial` are implemented in `src/polynomial.rs`,
generic over the coefficient ring, with the polynomials over $\mathbb{Q}$
and over $\mathbb F_p$; the tests over $\mathbb F_p$ are those of the
[prime fields](components/numbers/contract.md#prime-fields). Their
[contract](components/polynomials/contract.md) states the operations, the
limits, the storage cost, the expansion of terms and the tests, and that the
operations exist for coefficient rings whose zero test always decides.
`Context` and `Result` are those of
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
    fn measure(&self, a: &Self::Element) -> Storage;   // no context, no charge
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
  associated type `Undecided`; for a field that is not exact, that reason
  is the shared result type `Evidence`, given only as `NumericEvidence` or
  `Unknown` ([shared result types](components/shared-results/contract.md#the-reason-of-an-undecided-zero-test)).
- **The storage cost is required.** `measure` returns the cost of an
  element as a `Storage`, its nodes and logical bytes by the rules of
  [storage bytes](#storage-bytes). It depends only on the parent and the
  element, takes no context and charges nothing, as `StorageCost` does. An
  element whose cost cannot be computed in constant time keeps its cost from
  when it was built, and `measure` reads it. For $\mathbb{Q}$ it is the cost
  of a rational, $(1, \lvert n \rvert + \lvert d \rvert + 3)$. Shared
  algorithms take the costs of coefficients only from `measure`, so they
  need no bound beyond the trait on the elements, also when the elements are
  themselves polynomials.
- **Closed until 1.0.** The trait is sealed, so required methods can be added
  in later releases without breaking callers. Until 1.0, users cannot define
  their own coefficient fields. No method of either trait has a default
  body.
- **Charging.** Each method but `measure` takes the context last. Element
  operations check sizes before they work and charge for themselves. Shared
  algorithms (multiplication, powers by repeated squaring, differentiation,
  evaluation, and later division with remainder, GCD and modular powers)
  charge only for their own loop steps. Every amount depends only on the
  operands.
- **Division by zero.** In every field, `inverse` and `divide` fail with
  `DivisionByZero` on the zero of the field. A field with a structural zero test checks the
  divisor before any charge of the operation, and a field whose zero test is
  charged pays for the test first.
- **One shared implementation.** Differentiation, evaluation, powers and
  modular powers exist once, bounded by the trait. Shared code reaches the
  coefficients, their zero test and their storage cost only through the
  methods of the trait, obtains integers only as $n \cdot 1$ and never
  divides by an integer, so it stays correct in characteristic $p$.
- **The parent is the receiver.** Polynomial operations take
  `PolynomialRing<K>`, which holds the coefficient structure and the
  variable, as `&self`. A `Polynomial<K>` stores neither, and its type is
  opaque: polynomials are produced only by methods of their ring, and these
  methods assume that their arguments belong to `self`. Whether two parents
  match is checked only where a parent and an element are stored as a pair,
  as later in the command entry where it stores such a pair and in typed
  collection columns. In this release no layer stores one: the conversions
  between terms and polynomials take the ring as their receiver, and the
  command entry converts every polynomial back to a term with the ring that
  built it. A layer that stores such a pair calls the crate-internal pair
  check `require_same_parent` of `src/coefficient.rs`, which compares the
  two parents with `same_parent` and fails with `VariableMismatch` when they
  differ. The fault kind was appended in 0.2 together with the prime
  fields, the first parents that can differ, and no layer calls the check
  yet. So a parent parametrized at runtime, such as $\mathbb F_p$, needs no
  change of signature, and polynomial operations do not compare parents.
- **The prime fields** have this shape: `PrimeField` holds its prime
  modulus $p \lt 2^{32}$, its constructor decides that the modulus is
  prime, and its elements, the residues $0 \le r \lt p$, do not repeat
  it ([contract](components/numbers/contract.md#prime-fields)).
- **Later structures** take the same shape, and each implements `measure`
  with a formula of its own: number fields, including $\mathbb{Q}(a)$,
  whose `same_parent` compares the defining data and is charged;
  `FractionField<K>` with
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

## Algebraic numbers

**Status:** planned for release 0.2; not implemented. Algebraic numbers
build on the factorization of polynomials over $\mathbb{Q}$ and on real root
isolation, which are planned for the same release. Every step below uses
exact rational arithmetic only, never floating point.

Write $m$ for a minimal polynomial and $d$ for its degree. The principal
argument is $\mathrm{Arg} \in (-\pi, \pi]$, the principal root of a rational
$q$ is $q^{1/n} = \lvert q \rvert^{1/n} e^{i \mathrm{Arg}(q)/n}$, and
`sqrt(u)` is `rootn(u, 2)`.

### Identity

- **Real algebraic numbers.** The identity of a real algebraic number is
  the pair $(m, k_r)$: $m$ is its minimal polynomial over $\mathbb{Q}$,
  monic, with rational coefficients, irreducible and of degree at least 2,
  and $k_r$ is its position among the real roots of $m$ in ascending order,
  counted from 0. An algebraic number of degree 1 is a rational and is a
  number.
- **Complex algebraic numbers.** The identity of a complex algebraic
  number, one that is not real, is the pair $(m, k_c)$, where $k_c$ is its
  position among all the roots of $m$ in ascending order of the pair (real
  part, imaginary part), counted from 0. In this order the root of a
  conjugate pair with the negative imaginary part comes first, and a real
  root comes after the roots with the same real part and a negative
  imaginary part and before those with a positive one, between the two
  roots of each such conjugate pair. A real number is never of the complex
  type, and a complex algebraic number is never stored as a pair of real
  algebraic numbers.
- **Equality.** Two algebraic numbers are equal exactly when their
  identities are structurally equal, which needs no refinement, and equal
  values have equal identities. The identity holds $m$ in its monic rational
  form; bounds are computed from its primitive integer form, which is taken
  only for the computation.

### Order and cache

- **Order of algebraic constants.** Within rank 1 the algebraic constants
  come after the named constants, real before complex, then by degree, by
  the coefficients of $m$ and by the index. The order is total and
  deterministic and needs no refinement; it is not the order by size.
- **Cache.** Each algebraic number carries an isolating region as a cache:
  for a real number the canonical isolating interval of real root isolation,
  and for a complex number an isolating rectangle with dyadic corners. A
  root in the lower half-plane takes the mirror image of the rectangle of its
  conjugate, and a real root of $m$, where the complex order needs it, takes
  $(l, u) \times (-c_0, c_0)$ from its interval $(l, u)$, with $c_0$ as
  below. The cache is a deterministic function of the identity and never
  part of it. Refinement happens only in a workspace of the operation that
  needs it, so no result and no charge depends on what an earlier operation
  refined ([convention 8](conventions/public-api.md#8-determinism)). The
  cache counts in the storage cost of the number, by a formula that is fixed
  with the component.

### Isolating complex roots

Complex roots are isolated on the irreducible factors of a polynomial only,
by the argument principle with Sturm sequences (H. S. Wilf, 1978;
J. R. Pinkert, 1976; G. E. Collins and W. Krandick, 1992):

- The real roots come from real root isolation. The non-real roots in the
  upper half-plane lie in the rectangle $[-B, B] \times [c_0, B]$, where $B$
  is a [root bound](#bounds) and $c_0$ is the largest power of 2 that is not
  above $s/2$, with the separation bound $s$: every non-real root $\alpha$
  has $\lvert \mathrm{Im}(\alpha) \rvert \gt s/2$, so the band
  $0 \lt \lvert \mathrm{Im}(z) \rvert \le c_0$ holds no root. The roots in
  the lower half-plane are the mirror images.
- The rectangle is split into four, recursively. The number of roots in a
  rectangle is the winding number of $m$ along its boundary: along each
  edge, $m(z(t)) = A(t) + iB(t)$ with real polynomials $A$ and $B$, and Sturm
  sequences, computed with subresultants, give the Cauchy index of the edge.
  The count is taken only on rectangles with no root on their boundary,
  where the algebraic winding number equals the number of roots inside
  (M. Eisermann, 2012). At an end point of an edge a crossing counts half,
  and an edge on a vertical line along which $m$ takes real values counts 0.
- A split line through a root, also at the crossing of two lines, shows as a
  real root of $\gcd(A, B)$ on the line, which the real root count detects,
  and the line moves. The lines tried are the middle, then the middle
  $\pm w/4$, $\pm w/8$ and so on for a width $w$, and one of the first $d + 1$
  holds no root.
- Isolation always ends with the complete list of roots, builds no
  polynomial of degree above $d$, and has an a priori bound on the depth of
  subdivision, which can be checked against the limits before the work
  starts.

### Comparing values

Equality is structural, as stated above. The order by value, which sorts
real algebraic numbers by size and complex roots by real part and then
imaginary part, is decided by exact refinement in grades, and never by a
projection:

- Two real numbers with the same $m$ compare by index; with different
  minimal polynomials, their intervals are refined until they are disjoint.
- Two complex roots compare by their real parts first, then by their
  imaginary parts. While their real-part intervals meet, three grades decide
  in turn whether the real parts are equal: (1) the roots are conjugate, with
  the same $m$ and mirrored rectangles; (2) a rational vertical line holds
  both: for the simplest rational $a$ in the intersection of their real-part
  intervals, the greatest common divisor of the real and imaginary parts of
  the restriction of each factor to the line $\mathrm{Re}(z) = a$ has a root
  in the imaginary-part interval of that root; (3) the caches are refined
  until the real-part intervals are disjoint, which orders the roots, or
  until the sum of their widths is below $\delta_{\mathrm{Re}}$ of the
  [bounds](#bounds) while they still meet, which shows that the real parts
  are equal.
- No grade builds a polynomial of a degree above $\max(d_1, d_2)$. The third
  grade needs a precision that grows with $d_1^2 d_2^2$: for the minimal
  polynomials of $\sqrt{2} + i$ and $\sqrt{2} + i\sqrt{2}$, of degree 4, the
  bound is about $2^{-1469}$ and the refinement exceeds the default
  `max_integer_bits`. Such a comparison fails with `ResourceLimit`, never
  with a wrong answer, and a larger `max_integer_bits` lets it finish.
- No representation, isolation, equality test or comparison computes a
  projection, the polynomials of degree $d^2$ whose roots are the real parts
  or the imaginary parts of the roots of $m$. A projection appears only in an
  operation whose answer is that projection, such as the real part, the
  imaginary part or the squared modulus of a complex algebraic number.

### Bounds

| Use | Bound | Applied to | Degree |
| --- | --- | --- | --- |
| The band $c_0$ and the depth of subdivision | Mahler–Landau | the primitive integer form of $m$ | $d$ |
| Ordering real algebraic numbers with different $m_1$, $m_2$ | Mahler–Landau | $m_1 m_2$ | $d_1 + d_2$ |
| Selecting the root of the result of arithmetic on algebraic numbers | refinement until the enclosure holds one root of $\mathrm{sqf}(R)$, by exact counting; $s(\mathrm{sqf}(R))$ only as an a priori bound | the squarefree part $\mathrm{sqf}(R)$ of the resultant $R$, the product of its distinct irreducible factors in primitive integer form | at most $d_1 d_2$ |
| The third grade of equal real parts | $\delta_{\mathrm{Re}}$ | only the degrees, the leading coefficients and the root bounds | — |

The root of an arithmetic result is selected on $\mathrm{sqf}(R)$ and not on
the factor that holds it: before the selection it is not known which factor
holds the result, and a root of another factor can be closer.

**Mahler–Landau separation bound.** For a squarefree $f \in \mathbb{Z}[x]$ of
degree $d \ge 2$ with the Mahler measure $M(f)$:

```math
\mathrm{sep}(f) > \sqrt{3}\, \lvert \mathrm{disc}(f) \rvert^{1/2}\, d^{-(d+2)/2}\, M(f)^{-(d-1)}
```

With $\lvert \mathrm{disc}(f) \rvert \ge 1$ and Landau's inequality
$M(f) \le \lVert f \rVert_2$:

```math
\mathrm{sep}(f) > s(f) := \sqrt{3}\, d^{-(d+2)/2}\, \lVert f \rVert_2^{\,1-d}
```

(K. Mahler, An inequality for the discriminant of a polynomial, Michigan
Math. J. 11 (1964) 257–262; E. Landau, Bull. Soc. Math. France 33 (1905);
M. Mignotte, Mathematics for Computer Algebra, 1992.) So $c_0 = 2^{-k}$ for
the least integer $k$ with $3 \cdot 4^k \ge 4 d^{d+2} N^{d-1}$, where
$N = \lVert f \rVert_2^2$, which needs no square root: $2^{-7}$ for
$x^3 - 2$ and $2^{-8}$ for $x^4 + 1$.

**Cauchy root bound.** Every root $\alpha$ of
$\sum_{i \le d} a_i x^i$ satisfies
$\lvert \alpha \rvert \lt 1 + \max_{i \lt d} \lvert a_i / a_d \rvert$
(A.-L. Cauchy, 1829; C. Yap, Fundamental Problems of Algorithmic Algebra,
2000).

**Bound for equal real parts.** Let $\ell_j$ be the leading coefficient of
the primitive integer form of $m_j$ and $B_j$ an integer strict upper bound
on the moduli of its roots. $2\ell_1\ell_2(\mathrm{Re}(\alpha) - \mathrm{Re}(\beta))$
is an algebraic integer of degree at most $d_1^2 d_2^2$, whose norm is at
least 1 when it is not 0, so

```math
\lvert \mathrm{Re}(\alpha) - \mathrm{Re}(\beta) \rvert \ge \delta_{\mathrm{Re}} := \frac{1}{2\ell_1\ell_2} \bigl( 2\ell_1\ell_2 (B_1 + B_2) \bigr)^{-(d_1^2 d_2^2 - 1)}
```

unless the real parts are equal.

### Principal roots of rationals

A principal root of a rational has the call `sqrt(q)` or `rootn(q, n)` as
its canonical form, and the call constructor normalizes it cheaply, without
arithmetic on algebraic numbers:

1. $n = 1$ gives $q$;
2. $q = 0$ gives 0;
3. for $q \gt 0$, for each prime $p$ that divides $n$ and for which $q$ is
   the $p$-th power of a rational, $q^{1/p}$ and $n/p$ replace $q$ and $n$,
   until no such prime remains;
4. for $q \lt 0$ and $n = 2$, $\sqrt{q} = i\sqrt{-q}$;
5. for $q = -4t^4$ with a rational $t \gt 0$ and $n = 4$, the root is
   $t + ti$;
6. any other root stays a call.

For $q \gt 0$, after step 3, $x^n - q$ is irreducible by Capelli's theorem
(S. Lang, Algebra, chapter VI, §9): $x^n - a$ is irreducible over a field
$K$ exactly when $a \notin K^p$ for every prime $p$ that divides $n$, and
$a \notin -4K^4$ when $4$ divides $n$. The test is an integer $p$-th root, at
most about $\log_2 n$ of them. Steps 4 and 5 cover every principal root in
$\mathbb{Q}(i)$ that is not rational. The parsed `sqrt(2)` and the algebraic
number $(x^2 - 2, 1)$ are therefore the same call `sqrt(2)`, and the complex
algebraic number $(x^2 + 1, 0)$ embeds only as $(-1) \cdot i$, the same term
as the parsed $-i$.

Equal values give equal terms for every principal root of a positive
rational, for the principal roots of negative rationals whose binomial
$x^n - q$ is irreducible, and for the two classes $n = 2$ and $n = 4$. Two
known exceptions remain: `rootn(-8, 3)` stays a call, while the algebraic
number of the same value embeds as $1 + i\sqrt{3}$; and
$\mathrm{rootn}(-4, 4)^4$ stops at $(1 + i)^4$, since a power of a sum is not
expanded.

### Algebraic numbers as terms

An algebraic number becomes a term by these rules, which are the reverse
direction of the normalization of principal roots; none of them needs a
projection:

1. degree 1 gives the number;
2. degree 2, with $m = x^2 + px + r$, $a = -p/2$ and
   $\Delta = p^2/4 - r$: for $\Delta \gt 0$ the closed form
   $a \pm \sqrt{\Delta}$, by $k_r$; for $\Delta \lt 0$ the closed form
   $a \pm i\sqrt{-\Delta}$, by the sign of the imaginary part;
3. degree at least 3 with $m = x^n - q$: a real root is
   $\pm\mathrm{rootn}(q, n)$ for $q \gt 0$, by $k_r$ when $n$ is even and the
   positive one when $n$ is odd, and $-\mathrm{rootn}(-q, n)$ for $q \lt 0$
   and odd $n$; the non-real root with $q \lt 0$ and $k_c = n - 1$, the
   principal root, is $\mathrm{rootn}(q, n)$;
4. every other real algebraic number is a real algebraic constant;
5. every other complex algebraic number is a complex algebraic constant.

In rule 3, $\mathrm{rootn}(q, n)$ for $q \lt 0$ has the argument $\pi/n$ and
is not real, so the one real root is $-\mathrm{rootn}(-q, n)$, and the
principal root comes last in the order of (real part, imaginary part). So
the principal root of $-8$, the root $(x^2 - 2x + 4, 1)$, is
$1 + i\sqrt{3}$; $(x^4 + 1, 3)$ is `rootn(-1, 4)`; the real root of
$x^3 + 2$ is $-\mathrm{rootn}(2, 3)$, and its principal root is
`rootn(-2, 3)`. An algebraic constant is never rational, so it is an exact
number other than 0, as the [constants](#constants) need.

## Requests and results

**Status:** the [operands of a request](#the-operands-of-a-request), its
[order of checks](#the-order-of-the-checks), its
[answers and output lines](#answers-and-output-lines), the
[locations and cause frames](#locations-and-cause-frames) of its errors,
the [fallback line](#the-fallback-line) and the
[table of value kinds](#the-table-of-value-kinds) are implemented, as the
[contract of the command entry](components/command/contract.md) and the
[output lines](semantics.md#output-lines) state them: a request has an
operand table, an answer is an `Answer`, and an error has its entry frame.
The operations of this release read no role of the table, every answer is
a term, and no operation adds a nested frame. The extension of the grammar,
the start symbols by role, the roles of the planned operations and their
nested categories are planned for release 0.2 and not implemented: the
grammar of this release reads only values. The rules below are those that
the parser, the command entry and the operations of release 0.2 follow; the
[input syntax](semantics.md) and the contracts of the other components write
out the planned parts when they land. The commands named
here other than `eval`, `expand` and `diff` are planned commands of that
release. An input that 0.1 accepts reads the same, and the kinds of lines
that 0.1 writes keep their fields.

### One grammar, read by role

- **One grammar.** Every text operand of a request is read by the one
  grammar of the [input syntax](semantics.md#the-single-grammar-rule),
  which chooses its start symbol by the role of the operand. The names of
  the start symbols are working names; the input syntax fixes them when
  they land.

  | Start symbol | Reads | Used by |
  | --- | --- | --- |
  | `input` | a value, as in 0.1 | the input of an operation that reads a value, and every value role that no row below names |
  | `condition_input` | a [condition](#conditions) | the `input` and the `right` of `ineq` and of the `rel-` commands, and the condition column of an `answer` line read back |
  | `binding_input` | a binding `name = value` | the role `binding` |
  | `set_input` | an interval or a set of reals | the set operands of `interval`, `set`, `contains` and the set commands |
  | `field_input` | a number field `field(p, k)` | the role `field` |
  | `element_input` | an element `field_element(field(p, k), e)` | the self-contained text of an element read back |
  | `scope_input` | facts `x: positive, y: real` | the role `scope`, and the assumptions column of an `answer` line read back |
  | `names_input` | names `x, y`, or the empty text for none | the role `variables` |
  | `keyword_input` | one identifier | the roles `property` and `monomial_order` |

- **The call table, at reading.** The parser looks every head up in a call
  table while it reads: the names, the numbers of arguments and the roles
  of the arguments of the function registry, the three special forms, the
  heads of literals and the heads of conditions. An unknown head, a wrong
  number of arguments and an argument of the wrong class fail with
  `Syntax` when they are read. The checks of domains and of numeric
  arguments, such as the degree of `rootn`, come when the term is built,
  and every syntax error still comes before any term is built, as in 0.1.
  So an input with two failures reports the first in the order of reading:
  `rootn(x, 0) + foo(y)` fails with `Syntax` at the unknown head `foo`,
  and not with `OutsideDomain` at the degree 0.
- **Reserved words by position.** A word that is a valid identifier in 0.1
  is a symbol in every value position; new meanings arise only where 0.1
  fails, as the table of the [reserved names](#reserved-names) states.
- **Two tokens of lookahead.** A name followed by `(` is a call in a value
  position, and the start of a condition is decided by the same two tokens,
  as [the conditions](#conditions) state.

### Extensions of the grammar

| Extension | Spelling | Where it is read |
| --- | --- | --- |
| Calls | `head(arg, …)`, each argument read by the role that the call table gives its position | value positions |
| Constants | `pi` and `i` are constants; `undefined` only as a whole branch of `piecewise` | value positions |
| Conditions | `true`, `false`; `u REL v` with one of `==`, `!=`, `<`, `<=`, `>` and `>=`, not associative; `is_<property>(u)`, `defined(u)`; `not(c)`, `and(c, c, …)`, `or(c, c, …)` | `condition_input`; the first argument of `piecewise`; the operands of the connectives |
| Bindings | `name = value` | the arguments of `substitute` from the second on; `binding_input` |
| Real algebraic numbers | `root(p, k)` | value positions |
| Complex algebraic numbers | `croot(p, k)`; a general complex number is written `3 + 4*i` | value positions |
| Principal roots | `sqrt(u)` and `rootn(u, n)`, with no other spelling | value positions |
| Number fields and their elements | `field(p, k)`; an element in the generator `a`; `field_element(field(p, k), e)` | `field_input`; element positions; `element_input` |
| Intervals and sets | `Icc(a, b)`, `Ico(a, b)`, `Ioc(a, b)`, `Ioo(a, b)`; `Ici(a)`, `Iic(b)`, `Ioi(a)`, `Iio(b)`; `reals()`; `union(I1, …)`, with `union()` the empty set | `set_input` |

- **Calls.** Arguments are separated by `,`, with no trailing comma, and a
  call has no arguments only when its head takes none, as `reals()` does.
  Whitespace may stand between the name and `(`, as in 0.1. An unknown
  head fails with `Syntax` and the span of the name, and a wrong number of
  arguments with `Syntax` and the span of the whole call. Besides the
  eleven registered functions, the call table gives `piecewise` a condition
  and two values, `derivative` a value, a variable and a value,
  `substitute` a value and one or more bindings, and `root` and `croot` a
  polynomial and a value. Degrees, orders and indices are value arguments,
  checked by their canonical forms when the call is built, so
  `rootn(x, 1+2)` is `rootn(x, 3)`. The variable of `derivative` takes only
  an identifier, and a reserved name there fails with `Unsupported`, as in
  0.1. Each argument is one level deeper for `max_depth`, and the syntax
  nodes of a call count against `max_nodes`.
- **Orders.** The order of `derivative`, and the role `order`, must have a
  canonical form that is an integer from 0 to `max_exponent`, and the order
  0 gives the operand itself. A larger order fails with `ResourceLimit` on
  `max_exponent`; a negative order, an order that is not an integer, a
  constant and an order that holds a symbol fail with `OutsideDomain`, and
  no call is built. Unlike a symbolic degree of `rootn`, which builds a call
  ([rules of the call constructor](#rules-of-the-call-constructor)), a
  symbolic order builds none.
- **Bindings.** A binding of the wrong shape, with no `=`, a name position
  that is not an identifier, a reserved name, an empty value or a name
  bound twice, fails with `InvalidBinding` and the index of its operand. An
  error inside a value that is not empty is the error of that value, so
  `x = 1/0` fails with `DivisionByZero`. Bindings display as `x = v`,
  sorted by name. `=` stands only in a binding, and `==` is a comparison.
- **Algebraic numbers.** In `root(p, k)` and `croot(p, k)`, `p` is a
  polynomial with rational coefficients in exactly one symbol, which is
  local to the literal; `p` need not be irreducible. `k` is a position,
  counted from 0: among the distinct real roots of `p` in ascending order
  for `root`, and among its distinct complex roots in the order of their
  [identity](#identity) for `croot`. A literal embeds as
  [a term](#algebraic-numbers-as-terms): `root(x^2-2, 1)` is `sqrt(2)`,
  the same term as the parsed `sqrt(2)`, and `croot(x^2+1, 0)` is only
  $(-1) \cdot i$. An algebraic constant displays as `root(m, k)` or
  `croot(m, k)` with its monic minimal polynomial `m` written in `x` as the
  term core displays it, such as `root(1 - 3*x + x^3, 0)`. There is no
  `complex(re, im)`. The kinds of the errors for a polynomial that does not
  qualify and for an index out of range are fixed with the component.
- **Principal roots.** In an operand of an operation on algebraic numbers,
  `rootn(u, n)` with a positive integer degree evaluates to the principal
  root; in a term it stays a call, as
  [the principal roots of rationals](#principal-roots-of-rationals) state.
- **Number fields.** In `field(p, k)`, `p` is irreducible and `k` is the
  canonical index of the generator $\alpha$ among all the complex roots of
  `p`; a reducible or constant `p` fails with `OutsideDomain`. An element
  operand is a polynomial in the generator `a`. In
  `field_element(field(p, k), e)` the `a` is local and `e` is reduced, of a
  degree below that of the minimal polynomial, and this text is the
  display of an element. The kind of the error for a symbol other than `a`
  in `e` is fixed with the component.
- **Intervals and sets.** In the names of the interval heads, `c` is a
  closed end and `o` an open end, for the left end and then the right end;
  `Ici`, `Iic`, `Ioi` and `Iio` are rays, and `reals()` is the real line.
  The canonical form of each end point must be a real algebraic number. A
  lower end above the upper end fails with `InvalidInterval`; `Icc(a, a)` is
  a point, and `Ico(a, a)`, `Ioc(a, a)` and `Ioo(a, a)` are empty. A set
  displays as its interval when it is one, and otherwise as `union(…)` of
  its intervals sorted by their lower ends. The interval operands of
  `interval`, `set`, `contains` and the set commands read `set_input`, so
  the head states whether each end is open. The bounds `lower` and `upper`
  of `count-roots` are optional value roles, and a missing one is
  unbounded.

The new productions, in the notation of [the grammar](semantics.md#grammar);
`expression`, `term`, `unary`, `power`, `number`, `identifier` and the
lexical rules are those of 0.1, and the new tokens are `,`, `=`, `==`,
`!=`, `<`, `<=`, `>` and `>=`, with `:` a token only under `scope_input`:

```text
input           = expression ;
condition_input = condition ;
binding_input   = binding ;
set_input       = set ;
field_input     = field ;
element_input   = element ;
scope_input     = fact , { "," , fact } ;
names_input     = [ identifier , { "," , identifier } ] ;
keyword_input   = identifier ;

primary    = number | identifier | call | "(" , expression , ")" ;
call       = head , "(" , [ argument , { "," , argument } ] , ")" ;
head       = ? an identifier that the call table holds for a value position ? ;
argument   = ? the production of the role that the call table gives the
               position: expression, condition, binding or identifier ? ;
condition  = "true" | "false" | predicate | connective | comparison ;
comparison = expression , relation , expression ;
relation   = "==" | "!=" | "<" | "<=" | ">" | ">=" ;
predicate  = predicate_head , "(" , expression , ")" ;
predicate_head = "defined" | property ;
property   = ? "is_" followed by a property name of the assumption system ? ;
connective = "not" , "(" , condition , ")"
           | ( "and" | "or" ) , "(" , condition , "," , condition ,
             { "," , condition } , ")" ;
binding    = identifier , "=" , expression ;
fact       = identifier , ":" , identifier ;
field      = "field" , "(" , expression , "," , expression , ")" ;
element    = "field_element" , "(" , field , "," , expression , ")" ;
set        = interval | "reals" , "(" , ")"
           | "union" , "(" , [ interval , { "," , interval } ] , ")" ;
interval   = ( "Icc" | "Ico" | "Ioc" | "Ioo" ) ,
             "(" , expression , "," , expression , ")"
           | ( "Ici" | "Iic" | "Ioi" | "Iio" ) , "(" , expression , ")" ;
```

### Only additions

- **Accepted input keeps its meaning.** Every extension gives a meaning
  only to input that 0.1 rejects, as the
  [single-grammar rule](semantics.md#the-single-grammar-rule) requires:
  under `input`, every input that 0.1 accepts reads the same and has the
  same canonical form. Input that 0.1 rejects may give a value or another
  error: `sin(x)` fails with `Unsupported` in 0.1, and in 0.2 it is a call
  that holds a free symbol, so `eval` of it fails with `UnknownSymbol`.
- **Notation kept free.** The grammar takes no brackets, no braces, no
  quotes and no `:` in a value position, which stay free for the collection
  values of 0.3 and for the notation of matrices and vectors. It has no
  `..`, no juxtaposition, no infix keywords and no word for infinity or for
  the empty set, such as `inf` or `empty`.
- **Rules for later releases.** Five rules keep later releases within the
  same grammar:
  1. a new constant takes only a reserved name or a spelling that is an
     error in 0.1;
  2. a physical constant never takes a bare name such as `c` or `h`;
  3. a user function, which joins the call table, never takes the name of
     a condition head;
  4. `=` never stands for an equation, only in a binding, and an equation
     is written with `==`;
  5. the branch of a general power $u^{1/n}$ agrees with that of
     `rootn(u, n)`.

### The operands of a request

- **Fields.** `Request` keeps every field, the constructor
  `Request::new(operation, variable, input)` and the modifiers of 0.1, and
  `Settings` stays an empty record, so a value other than the default still
  fails with `Unsupported`. A new public field `operands: Vec<Operand>`
  holds the operand table, which `Request::new` leaves empty. `Operand` is a
  `#[non_exhaustive]` record that derives `Clone`, `Debug`, `PartialEq` and
  `Eq`, as `Request` does, with the public fields `role: String` and
  `text: String` and the constructor `Operand::new(role: &str, text: &str)`.
  `Request::with_operand(self, role: &str, text: &str) -> Self`, marked
  `#[must_use]` as the other modifiers are, appends an entry. `Operand` and
  `Answer` are in `kalyx::command`, as `Settings` is, and not in the crate
  root.
- **Indices.** The operand index 0 is `input`, and an index $k \ge 1$ is
  `operands[k-1]`.
- **Signatures.** Each operation declares its signature in its component
  contract: the roles that it reads, whether each role is required,
  optional with a stated default, or repeatable, and the start symbol that
  reads it. `operation` and `variable` stay typed fields.
- **Text is an operand.** Every text that a caller writes is an operand
  with a role, read by the one grammar with the start symbol of its role,
  and the only typed fields of a request are those of 0.1. Settings change
  the meaning of every operation alike, while an operand is data of one
  operation, so the scope of assumptions of an operation is an operand.
- **The scope.** The role `scope` is optional, and its default holds no
  facts. It is written `x: positive, y: real`: each name follows the rule
  of [symbol names](components/terms/contract.md#symbol-names) and is not a
  reserved name, and each property is a name of the list of the assumption
  system. An unknown property fails with `Syntax`, and properties of one
  name whose intersection is empty fail with `ContradictoryAssumptions`,
  each with its span.
- **Rings.** A multivariate ring takes two required roles: `variables`, a
  list of names that may be empty, where the empty text is the ring without
  variables and a repeated name fails with `Syntax`; and `monomial_order`,
  one of `lex`, `grlex` and `grevlex`, where any other name fails with
  `Syntax`. The coefficients are $\mathbb{Q}$ in 0.2; an optional role
  `coefficients` arrives in 0.4.
- **Orders and centers.** The role `order` is optional in `f-diff`, with the
  default 1, and the truncation order of `f-series` has the same name; both
  follow the [rule of orders](#extensions-of-the-grammar). The role
  `center` is required in `f-series` and must be an exact term without
  symbols, such as `pi/2`; a symbol in it fails with `UnknownSymbol`.
- **Role names.** The planned operations share 19 role names: the value
  roles `point`, `order`, `center`, `inner`, `divisor`, `right`, `value`,
  `lower`, `upper`, `width`, `index`, `degree` and `embedding`; `binding`;
  `scope`; `variables`; the keyword roles `property` and `monomial_order`;
  and `field`. The `input` and the `right` of `ineq` and of the `rel-`
  commands read conditions, and the set operands of `interval`, `set`,
  `contains` and the set commands read sets.
- **Limits.** New bounds fall on the existing fields, and `Limits` keeps its
  nine fields: orders, degrees and root indices on `max_exponent`; the
  entries of the operand table and the checks of required roles on
  `max_work`; the sum of the bytes of the text operands on
  `max_input_bytes`; scopes on `max_storage_bytes`; and nested operations
  on `max_frames`.
- **The command-line program** of 0.2 reaches only the operations that read
  no more than the variable and the input.

### The order of the checks

The command entry checks a request in this order and stops at the first
failure:

1. The settings, as in 0.1.
2. The operation name, as in 0.1.
3. The entries of the operand table, in the order of the table: the command
   entry charges one work unit for each entry, then looks up its role. An
   unknown role fails with `Fault(Unsupported)`, as an unknown operation
   does, and a second entry of a role that is not repeatable fails with
   `Fault(Syntax)`; both have no span, and their location is the index of
   the entry, in an `error-at` line.
4. The required table roles of the signature, other than `input`, one by
   one in the order of the signature: the command entry charges one work
   unit for each, then checks that it occurs. A missing role fails with
   `Fault(Syntax)`, with no span and no location, and its message names the
   role of the signature. The operations of 0.1 have no table roles, so
   this step charges nothing for them. An empty `input` is not checked
   here: the parser reports it in step 7, as in 0.1, with the empty span at
   the end of the input.
5. The variable: an operation that reads it checks it by the rule of symbol
   names, without a charge, and its ring charges it, as in 0.1.
6. When the operand table is not empty, the sum of the bytes of all text
   operands, the input and every entry, is checked against
   `max_input_bytes`; this check is not a charge point. A larger sum fails
   with `ResourceLimit` on `Field(max_input_bytes)`, with no span and no
   location and the amount `Required(n)` for the sum $n$. The sum is
   accumulated with checked addition, and on an overflow the amount is
   `Bound(u64::MAX)`, which fails under every `max_input_bytes`,
   `u64::MAX` included. With an empty table the command entry skips this
   step, and the parser checks `input` before it reads it, as in 0.1, with
   the same fields and at the same point.
7. The operands, read in the order of the signature; an error carries the
   index of its operand.
8. The operation itself.

- **No fallback.** A missing operand never falls back to another operation,
  and an entry outside the signature is an unknown role.
- **Requests of the form of 0.1.** A request with an empty table whose
  signature has no required table role runs the steps of the command entry
  in the order and with the charges of 0.1. Such are the requests of the
  three operations of 0.1 with an empty table, and so every request of
  `vectors/r02.tsv`. Whether all the work of such a request stays that of
  0.1 once the parser reads the call table is not part of this: work is not
  compared across releases.
- **The first charge.** Every entry of the table and every required role is
  charged before it is checked, so an error of a role comes after a charge
  point, and with cancellation set the request fails with `Cancelled`. A
  request whose table is not empty, or whose signature has a required table
  role, fails before its first charge only for settings other than the
  default and for an unknown operation; every other request keeps the list
  of 0.1.
- **Determinism.** A result depends on the order of the table only through
  the operand indices and the order of the entries of one repeatable role.

### Answers and output lines

- **The outcome.** `Outcome` stays a struct with private fields that only
  `execute` builds; its version accessors and the signatures of `execute`
  and `serialize` stay as they are. `result()` returns
  `&Result<Settled<Answer>>`, and `into_result()` returns the same result
  by value.
- **Answers.** `Answer` is a `#[non_exhaustive]` enum with one variant for
  each value kind that an operation can return. `Answer::Term(Term)` is the
  one variant of 0.1, and every value that the operations of 0.1 return is
  one. A result therefore falls into one of three classes, a value of some
  variant, a state or an error, and new variants add no class. Each
  operation names the variant that it returns in its component contract
  and in the index of operations of the command entry.
- **States.** The result states are those of `MathState` only. A status
  that carries data, such as the completeness of a list of roots or an
  unknown truth value, is part of the answer, so an answer whose
  completeness is unsolved is still a value.
- **Errors.** `ErrorKind` does not change. The fault kinds of 0.2, such as
  `OutsideDomain`, `InvalidBinding`, `InvalidInterval` and
  `ContradictoryAssumptions`, are new variants of `FaultKind`, of the class
  `Input`, and fall under `Fault(_)`.

The common rules of the [output lines](semantics.md#output-lines) do not
change: one line of UTF-8 text per request, fields separated by one tab and
the line ended by one line feed, versions in decimal, the same escaping,
every byte charged as output with the output of a line exactly its length,
no partial line, and the same bytes for the same outcome under every
context. The kinds of lines that 0.1 writes keep their number of fields and
the form of every field, and new information comes as a new kind of line or
as a new field at the end of a line:

| Kind | Fields | Written for |
| --- | --- | --- |
| `value` | 5, as in 0.1: `value`, the three versions and the display of the term | an answer `Answer::Term` |
| `state` | 5, as in 0.1: `state`, the three versions and the name of the state | a state |
| `error` | 11, as in 0.1: `error`, the three versions, the kind, the span, the limit, the scope, the allowed value, the amount and the message | an error without a location, or whose location is the operand 0 with no nested frame |
| `answer` | 8: `answer`, the three versions, KIND, TEXT, CONDITION and ASSUMPTIONS | an answer of every value kind other than a term |
| `error-at` | 12: `error-at`, fields 2 to 11 as in an `error` line, and LOCATION | every other error |

- **The `answer` line.** KIND is the name of the value kind in
  [the table of value kinds](#the-table-of-value-kinds): lowercase ASCII
  letters and `-`, never renamed and never reused. TEXT is the display of
  the value. CONDITION is the condition of the value in the spelling of
  [the conditions](#conditions), `true` for a function value whose
  condition is true, and `-` for a kind that has no condition part.
  ASSUMPTIONS is the scope of the value in the spelling of the role
  `scope`, and `-` for a kind that has no scope part or for a scope
  without facts. The three fields hold printable ASCII. TEXT parses by the
  input grammar or by the display grammar that the table of value kinds
  names for its kind; CONDITION and ASSUMPTIONS read back with
  `condition_input` and `scope_input`. The condition and the scope are
  fields of their own, so a display text never holds them.
- **The `error-at` line.** Fields 2 to 11 have the meaning and the form of
  fields 2 to 11 of an `error` line: the three versions, the kind, the
  span, the limit, the scope, the allowed value, the amount and the
  message, so a program that reads `error` lines reads these ten fields at
  the same positions. Field 12, LOCATION, is

  ```text
  location = operand , { ">" , frame } ;
  operand  = decimal ;                (* the operand index of frames()[0]; 0 is input *)
  frame    = name , "#" , decimal ;   (* frames()[1..]: a nested operation or step, its operand index *)
  name     = ? [a-z][a-z0-9-]* : an operation of the dispatch table
               or a name of the fixed list of nested categories ? ;
  decimal  = ? ASCII digits without a sign, separators or leading zeros,
               written as the versions are ? ;
  ```

  LOCATION holds only decimal numbers, `>`, `#` and names that the library
  defines, so it needs no escaping. Its `operand` is the operand index of
  the first [cause frame](#locations-and-cause-frames), whose operation is
  the operation of the request and is not written, and the nested frames
  follow in order. The span, field 6, counts bytes of the text of the
  operand that the innermost frame names, and is `-` when the error has no
  span.
- **Examples.** In these lines `⇥` stands for a tab; the kind names and the
  values of the `answer` lines are only illustrations:

  ```text
  value⇥0⇥0⇥0⇥1/2
  answer⇥0⇥0⇥0⇥function-value⇥log(x)⇥x != 0⇥-
  answer⇥0⇥0⇥0⇥function-value⇥log(x)⇥x != 0⇥x: positive
  error⇥0⇥0⇥0⇥Syntax⇥1..2⇥-⇥-⇥-⇥-⇥<message>
  error-at⇥0⇥0⇥0⇥Syntax⇥0..3⇥-⇥-⇥-⇥-⇥<message>⇥1
  error-at⇥0⇥0⇥0⇥Unsupported⇥-⇥-⇥-⇥-⇥-⇥<message>⇥2
  error-at⇥0⇥0⇥0⇥OutsideDomain⇥3..5⇥-⇥-⇥-⇥-⇥<message>⇥0>ineq#0
  ```

  They are a value line of 0.1; a function value with the term `log(x)`,
  the condition $x \ne 0$ and no scope; the same function value built by
  `fexpr` under the scope `x: positive`, which `fexpr` does not read, so
  the condition stays `x != 0` and the scope is its own field; an error
  line of 0.1; an error at bytes 0 to 3 of the first entry of the operand
  table; an error of the second entry without a span, such as an unknown
  role; and a nested error, where the left relation of `rel-and` fails in
  `ineq`.
- **The answer vectors of 0.1.** The 58 requests of `vectors/r02.tsv`
  use only `eval`, `expand` and `diff` and write only `value` and `error`
  lines. For each of them the result, the kind of line, the number of
  fields and every field other than the message stay as `v0.1.0` writes
  them. The message is not part of this, since its wording is not part of
  the interface. The replay of the vectors compares the canonical form,
  the kind of the error and the fields of the limit, as in 0.1; the display
  text and the spans stay as they are because the grammar only adds and the
  display rules of terms and the span rules of the parser do not change for
  the input of 0.1.

### Locations and cause frames

`Error` keeps `kind()`, `span()`, `message()` and `exceeded()` and gains
`frames()`, which returns `&[CauseFrame]`, the cause frames of the error,
outer first. A `CauseFrame` is a `#[non_exhaustive]` record of a frame name
and an operand index, with a constructor and accessors only. It belongs to
the errors component, together with `Error`, so the crate root re-exports
it; the name differs from that of `kalyx::context::Frame`, the token that
`enter_frame` returns.

- **The entry frame.** The command entry adds the first frame, which records
  the operation of the request and the index of the operand where the error
  arose: an entry of the table that fails its check, an operand that fails
  to read, or an error of the operation that belongs to one operand. An
  error that concerns no operand, of the settings, the operation name, a
  missing role, the sum of the bytes or the variable, has no frame, and
  neither has an error of a library function that is called directly.
- **Nested frames.** The other frames are nested frames: each records an
  operation, or a fixed step of the library, that an operation enters, and
  the index of the operand there. The left relation of `rel-and` that fails
  in `ineq` has the location `0>ineq#0`.
- **Records only.** Frames are records on the error. They are not opened
  with `enter_frame`, are not charged and do not count against
  `max_frames`, so the work and the line bytes of the requests of 0.1 do not
  change.
- **The span.** `span()` keeps its signature and counts bytes of the text of
  the operand that the innermost frame names; with no frame, or with only
  the entry frame of the index 0, that text is the input, as in 0.1. The
  command-line program of 0.3, whose spans count bytes of a whole line,
  converts them from the index and the offset.

### The fallback line

The [fallback step](components/command/contract.md#the-fallback-line) does
not change: when the line of a failed request cannot be written under the
context of the request, the host writes it again under
`Context::new(Limits::new(), CancelFlag::new())`. The step stays sound
because the length of an error line depends only on constants of the
library, and not on the input or on the limits that the caller sets:

- **No text of the caller.** An error line holds no display text, and
  neither the message nor the `Parameter(name)` of a `ResourceLimit` holds
  any text that the caller gave: the operation name, the variable, a role
  name or the text of an operand. Text is pointed at only by the span and
  the location. Every place in the library that builds a
  `LimitId::Parameter`, through `check_parameter` or directly, takes its
  name from one fixed list of parameter names of the form `[a-z][a-z0-9_]*`,
  which the contract of the command entry keeps with its fallback line from
  the first place that builds one.
- **Frame names from the library.** A nested frame takes the name of an
  operation when its step is an operation of the dispatch table, and
  otherwise a name from a fixed list of category names of the library. A
  frame name is never a binding name, a variable, a role name of the
  request or the name of a user function. A category name never equals the
  name of an operation, and a later operation never takes a category name.
  Every frame name has the form `[a-z][a-z0-9-]*`, as every operation name
  of the release has.
- **A bound $d$ on the nested frames.** The number of nested frames of an
  error, the number of `>` in its location, is at most $d$, which is fixed
  together with the list of nested categories in the contract of the
  command entry. $d$ is not taken from `max_frames`, which the caller can
  set to any `u64`, while the fallback line is written under
  `Limits::new()`. Two conditions make $d$ independent of the input and of
  the limits:
  1. no nested category occurs twice along one chain of an error, so $d$ is
     at most the number of nested categories;
  2. nesting in the syntax adds no frame: nesting inside one operand, of
     parentheses, calls and the arguments of connectives, is shown only by
     the span, and a frame is added only where an operation enters a nested
     category through a fixed step of the library.

  A user function of 0.3 that made nesting follow the input recursively
  would break the first condition, and so change the fallback step.

So the bytes of an `error-at` line are bounded by the longest kind, limit,
message and frame name of the library and by $d$, and an `error` line is
shorter. The contract of the command entry states the bound with its
current values and keeps it at most 65,536 bytes, the default
`max_output_bytes`. Since the fallback line charges one work unit per
byte, it also fits the default `max_work` of 100,000 units, and under a
fresh flag without a deadline its writing reports neither `Cancelled` nor
`DeadlineExceeded`.

### The table of value kinds

Every value kind that an answer can have, and every shape of a term that has
a display rule, is a row of one table, the
[table of value kinds](semantics.md#value-kinds) of the input syntax and
semantics, and a test checks the table against the code:

- **Columns.** A row holds the name of the kind, which is the KIND of an
  `answer` line; whether it is an answer or a shape in a term; its
  component; its kind of line; whether it has a condition part and a scope
  part; the name of its display test; and how its display text reads, in
  one of two forms: "the input grammar reads it back", with the name of its
  round-trip test, or "display grammar", with the place of that grammar in
  [the input syntax](semantics.md) or in the component contract and the
  name of its parse test. So the display text of every value kind can be
  parsed. A composite result without an input spelling, such as `divrem`,
  `gcdex` or `root-list`, takes the second form.
- **Granularity.** Each kind with a display rule has one row, marked as an
  answer or as a shape in a term, and each composite result is a kind of
  its own, not an instance of a generic tuple.
- **Rows with their code.** The change that delivers a kind adds its row in
  the same change. Every variant of `Answer` has exactly one row, which a
  test checks.
- **Start and close.** The table starts with the answer `term` and the
  five shapes of terms: number, symbol, power, product and sum. The
  release closes it with its file, commit and number of rows, and the value
  model and the encoding of 0.3 start from that.
- **Display rules** are written in the component contracts; the table only
  links to them.
- **Enums.** Every public enum is `#[non_exhaustive]`, with `ZeroTest` the
  one exception
  ([convention 3](conventions/public-api.md#3-extensible-enums-and-records)).

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
| `max_input_bytes` | bytes of the request's input; with a nonempty operand table, of all its text operands together | 65536 |
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
has one formula that depends only on the value and, where the formula needs
it, its parent structure, never on the platform or the memory layout. A
value that carries everything its formula needs implements `StorageCost`; a
value whose formula needs its parent structure takes its cost from a method
of the parent: a coefficient from `measure` of its coefficient ring, and a
polynomial from `storage` of its polynomial ring, which holds the variable
name. The context receives computed costs and never computes a formula or
calls back. Write $\lvert x \rvert$ for
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
  The number of terms of a polynomial is bounded through this cost. Over a
  coefficient ring other than $\mathbb{Q}$, a coefficient $c$ costs the
  `measure` $(n_c, b_c)$ of the ring in place of $(1, \mathrm{rb}(c))$.
- An integer $z$ costs $(1, \lvert z \rvert + 4)$, the cost of the rational
  $z/1$, wherever it occurs. A result of several integers, such as a
  quotient with its remainder, a GCD with its Bézout coefficients or a
  congruence, costs the sum of the costs of its integers, and an outcome
  without an integer, such as an inconsistent system of congruences or a
  quotient that is not exact, costs $(1, 4)$. The
  [numbers](components/numbers/contract.md#storage) list the results of the
  integer kernel.
- An element of a prime field $\mathbb F_p$, a residue $0 \le r \lt p$,
  costs $(1, \lvert r \rvert + 4)$, the cost of the integer $r$; the
  modulus belongs to the parent and is not counted. This is the `measure`
  of `PrimeField`.
- An element of a number field $\mathbb{Q}(a)$ costs its representative: the
  univariate polynomial over $\mathbb{Q}$ in the generator, of degree below
  that of the minimal polynomial, by the formula of univariate polynomials
  above, with the generator as its variable. The minimal polynomial belongs
  to the parent and is not counted. Number fields are planned; this is the
  formula that their `measure` is to use.
- The formulas of strings, lists, records and session bindings are fixed in
  0.3, where the value encoding uses the same formulas; those of matrices in
  0.4.

A formula becomes part of the compatibility contract with the release tag of
its component. Changing one changes which limit is reached first, so it is a
change of the answer vectors, made on purpose.

The retained totals replace bounds of the earlier implementation: its bound
on the bytes of one value, `max_symbolic_bytes`, is the case of
`max_storage_bytes` in which nothing else is retained, and its separate
bounds on degrees, terms and conditions are derived from `max_exponent` and
`max_nodes`, as the
[mapping of its limits](../vectors/README.md#limits-of-the-earlier-implementation)
states.

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
  Within the package, only the command entry and the command-line program
  may construct a `Context` (the guard rejects every other path it can see);
  the command entry never does: its caller, such as the command-line
  program, creates one context per request, and library code charges the
  context that it is given.

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
`message()`, `frames()` and `exceeded()`; `exceeded()` is `Some` exactly when
the kind is `ResourceLimit`, and `frames()` lists the
[cause frames](#locations-and-cause-frames), whose entry frame the command
entry adds.

- `ErrorKind` is `ResourceLimit`, `Cancelled`, `DeadlineExceeded` or
  `Fault(FaultKind)`. The first three are request failures, and only the
  context constructs them.
- `FaultKind` has seven foundation kinds in 0.1: `Syntax`, `UnknownSymbol`,
  `DivisionByZero`, `NonIntegerExponent` (the exponent is not an integer
  constant), `NotPolynomial`, `Unsupported` and `Internal`. Features append
  their own kinds in the release that needs them. In 0.2 the integer kernel
  of the exact numbers has appended `OutsideDomain`, and the pair check of
  the coefficient fields `VariableMismatch`; the others are planned:
  `ContradictoryAssumptions`, `InvalidBinding` and `InvalidInterval` in 0.2,
  `StaleEnvironment` and `DimensionMismatch` in 0.3, and `InvalidMatrix` and
  `SingularMatrix` in 0.4.
- Both enums are `#[non_exhaustive]`, and `class()` sorts every kind into
  one of three classes: `Context` for the request failures, `Input` and
  `Internal`.
- `Error::new(kind: FaultKind, span, message)` takes only a `FaultKind`,
  and no public path builds a request failure, so
  `Error::new(ErrorKind::Cancelled, ..)` does not compile; a `compile_fail`
  documentation test with the expected error code checks this.
- `Error` does not derive `PartialEq`, `Eq` or `Hash`, because it carries
  message text. Tests compare `kind()`, `span()`, `frames()` and
  `exceeded()`, never the wording of the message.

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
crate and are only extended afterwards; no domain defines a synonym.
`Evidence` and `Truth` are implemented in `src/shared.rs`, and their
[contract](components/shared-results/contract.md) states their
combinations and tests; `Completeness` is planned for 0.2, and `Guarantee`
for 0.3.

- All four are `#[non_exhaustive]`. `Guarantee` is `Exact`, `Certified`,
  `Estimated` or `Heuristic`; `Evidence` has at least `Proved`, `Refuted`,
  `NumericEvidence` and `Unknown`; `Truth` is `True`, `False` or `Unknown`.
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

The command entry maps an outcome to the state of the job that runs it, by
class: a value to completed, with its line; `Settled::State` to completed,
with the state attached; `ResourceLimit` and every `Fault` to failed, with
its line; and `Cancelled` and `DeadlineExceeded` to the terminal states that
the contract of the command entry defines together with krepi: its
[Table 1](components/command/contract.md#table-1-outcomes-and-the-terminal-states-of-a-job)
maps them to `cancelled` and `resource_exhausted`, and the contract states
the terminal state of a job of several requests.

A value of any variant of `Answer` has a `value` line for a term and an
[`answer` line](#answers-and-output-lines) otherwise, and an error has an
`error` or `error-at` line; these lines are implemented, and every answer
of this release is a term. The classes take in what later releases add: a
new variant of `Answer` or of `MathState`, and a new `FaultKind` of the
class `Input` or `Internal`, fall into an existing class and leave Table 1
as it is; Table 1 changes only for a new request failure (a new kind of
the class `Context`), a new variant of `Settled`, a new fault kind of
another class or a new terminal state for an existing class. An answer whose completeness is unsolved, such as an
incomplete list of roots, is a value, and its job completes: the terminal
state says whether the request finished, not whether its answer is
complete.

In 0.1, function-call syntax, the reserved names `pi`, `i` and `undefined`,
an unknown operation and a non-default setting fail with `Unsupported`, and
a missing operand fails with `Syntax`. The checks of the operand table are
implemented: an unknown role fails with `Unsupported`, as an unknown
operation and a non-default setting still do, and a second entry of a role
that is not repeatable and a missing required role fail with `Syntax`. In
0.2 (planned), calls and the constants have a meaning, and an unknown head
of a call and a wrong number of arguments fail with `Syntax`, as a missing
operand does.
