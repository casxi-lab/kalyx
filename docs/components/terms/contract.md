# Terms

This contract states the term core of kalyx: the one representation of
numbers, symbols, integer powers, products and sums that parsing,
canonicalization, expansion and differentiation produce; the canonical forms
that its constructors keep; the total order and the equality of terms; their
display text; and their cost in storage and in work. It applies to the module
`src/term.rs` with its submodules in `src/term/`. The
[architecture](../../architecture.md#term-representation) places the
component among the foundations and states its design rules, which this
contract writes out as invariants, and the
[public API conventions](../../conventions/public-api.md) state the rules that
every public interface follows. The limits and the charges belong to the
[context](../context/contract.md), the errors to the
[errors and result states](../errors/contract.md), and the numbers in a term
to the [exact numbers](../numbers/contract.md).

**Status.** Implemented in `src/term.rs` and `src/term/`, at tier A1 (tested
with a written contract); its canonical forms are planned for tier A2 in
release 0.2. The term core is written anew for kalyx after the design rules of
the architecture: no code and no test is taken over from the earlier
implementation, so [PORTING](../../../PORTING.md) has no row for it. Its
first caller in the library is the [parser](../syntax/contract.md), which
builds the term of every input through its constructors; the
[command entry](../command/contract.md) reads the terms of its results and
writes their display text.

## Scope

- **Included.** The type `Term` and its kinds; the constructors of numbers,
  symbols, sums, products and integer powers, and negation, difference and
  quotient built on them; the canonical forms, with the scaling of sums by
  numbers, the primitive parts of sums, the strict evaluation of numbers and
  the witnesses of negative exponents; the total order and
  equality; the set $N(t)$ of the bases that occur with a negative exponent;
  the display text; the accessors of the structure; the storage cost; and
  drop.
- **Excluded, with their owners.**
  - Reading input text into terms, with the input syntax, its spans,
    function-call syntax and the reserved names in input: the
    [parser](../syntax/contract.md), whose grammar is stated in
    [the input syntax](../../semantics.md).
  - Expansion, differentiation and the conversion between terms and
    polynomials: the [polynomials](../polynomials/contract.md).
  - The serialization of outcomes as output lines: the
    [command entry](../command/contract.md).
  - Function calls (their constructor, their simplification and the function
    registry), the constants $\pi$, $i$ and `undefined` of rank 1,
    assumptions, and the explicit operation that removes negative exponents
    under conditions: the term core extension and the function-expression
    baseline, release 0.2.
  - Simplification beyond the canonical forms: the rewriting engine, release
    0.5.
  - The executable specification of the canonical forms (tier A2): release
    0.2.

## Interface

The module `kalyx::term` holds:

- `Term`, with
  - the constructors `Term::number(value, context)`, which takes a
    `Rational`, `Term::symbol(name, context)`, `Term::sum(terms, context)`
    and `Term::product(terms, context)`, which take a slice of terms, and the
    methods `power(exponent, context)`, with an `i64` exponent,
    `negate(context)`, `subtract(other, context)` and
    `divide(other, context)`, each of which returns `Result<Term>`;
  - the charged traversals `compare(other, context)`, which returns
    `Result<Ordering>`, `equals(other, context)`, `display(context)`, which
    returns `Result<String>`, and `negative_bases(context)`, which returns
    $N(\mathrm{self})$ as a sorted `Result<Vec<Term>>`;
  - the accessors `kind()`, `size()`, `depth()`, `has_negative_power()`,
    `children()`, `as_number()`, `as_symbol()`, `as_power()`,
    `as_product()` and `as_sum()`, which read the node, take no context,
    charge nothing and return borrowed parts;
  - `Clone`, which only increments a count, a shallow `Debug`, and
    `StorageCost`;
- `TermKind`, `#[non_exhaustive]`, with the variants `Number`, `Symbol`,
  `Call` (reserved), `Power`, `Product` and `Sum`, the method `rank()`, and
  `Clone`, `Copy`, `Debug`, `PartialEq`, `Eq` and `Hash`.

Every constructor and traversal takes the context last
([convention 1](../../conventions/public-api.md#1-request-context-last)).
`Term` implements neither `PartialEq`, `Eq`, `PartialOrd`, `Ord` nor `Hash`
([convention 14](../../conventions/public-api.md#14-canonical-representation-and-equality)):
the `compile_fail` documentation test of `Term` checks that `==` does not
compile (`E0369`). `Term` is not `Send`: a compile-time assertion in
`src/term.rs` fails once it is, and a second `compile_fail` documentation test
checks that a term cannot move into a thread (`E0277`).

The accessors give what the parser, the polynomials and the command entry
read: `as_number()` the value of a number, `as_symbol()` the name of a
symbol, `as_power()` the base and the exponent, `as_product()` the
coefficient and the factors, `as_sum()` the constant, the coefficients and
the cores of the monomials, and `children()` the children of any node. They
return references and plain values; there is no view type with a lifetime
parameter.

Crate-internal: the shape `TermShape::Call(CallHead { name, class })` of a
reserved call node, with the class `CallClass`, which is `Registered` or
`Formal` and `#[non_exhaustive]`, and the test-only constructor
`reserved_call` that alone builds one; the check of an exponent against
`max_exponent` and the width of `i64`, through the crate-internal
`Context::check_width_at` of the [context](../context/contract.md#interface);
and, for the [parser](../syntax/contract.md), the rule of symbol names
(`starts_name`, `continues_name`, `is_digit` and `character_length`),
`is_reserved`, and `integer_exponent`, which reads an integer as an exponent
under the same check, so the parser and the term core cannot disagree on a
name or an exponent; and, for the [polynomials](../polynomials/contract.md),
`check_name`, the check of a whole name that `Term::symbol` makes, with
which a polynomial ring checks its variable.

The crate root re-exports nothing of the component.

## Rules

### Representation

- **One shared immutable tree.** A `Term` is a reference-counted node,
  `Term(Rc<TermNode>)`, with a private field. A node holds its shape, its
  children and four cached values. The shape is the kind with the data that
  the node holds itself: the value of a number, the name of a symbol, the
  head of a call, the exponent of a power, the coefficient of a product, or
  the constant of a sum and the coefficients of its monomials. The children,
  a `Vec<Term>`, are the base of a power, the factors of a product, the cores
  of the monomials of a sum and the arguments of a call. The cached values
  are the tree size, the depth, the logical bytes and whether the term holds
  a power with a negative exponent. A node never changes after it is built.
- **Sharing is invisible.** Cloning a term increments a count, and subterms
  may be shared, but no operation consults whether two terms share a node:
  equality and order compare structure, and every charge is the same for a
  shared and a separate node
  ([convention 8](../../conventions/public-api.md#8-determinism)). There is
  no intern table, no hash container and no global or thread-local state
  ([convention 9](../../conventions/public-api.md#9-no-global-state)): two
  equal terms built apart are two nodes that compare equal.
- **Threads.** `Rc` is not `Send`, and so neither is `Term`. If terms ever
  cross threads, the private pointer becomes an `Arc` and nothing public
  changes.

### Kinds and the total order

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
existing kinds. `compare` orders terms by rank first, and within a rank:

- numbers by value, through the charged `Rational::compare`;
- symbols by the bytes of their names, a proper prefix first;
- calls by the bytes of the head name, then the class (`Registered` before
  `Formal`), then the arguments one by one, then the number of arguments;
- powers by base, then exponent;
- products by their factors one by one, then the number of factors, then the
  coefficient;
- sums by their monomials one by one, each by its core and then its
  coefficient, then the number of monomials, then the constant.

"One by one" is lexicographic over the common positions: the first pair that
differs decides, and the counts decide only when every common pair is equal.
The order is total on canonical terms, and `compare` gives `Equal` exactly
for structurally equal terms. `equals` is `compare` giving `Equal`; since
canonical forms are unique, structurally equal terms are the same term.

### Products

`Term::product` builds the canonical product of its operands; `negate`
multiplies by $-1$ and `divide` multiplies by the power $-1$ of the divisor,
and the power of a product returns its factors here.

1. **Flattening.** The operands are taken from a work list in order. A number
   multiplies into the coefficient, which starts at 1. A product multiplies
   its coefficient into the coefficient and puts its factors on the work
   list. A sum $s$ is taken as $s = c \cdot p$, its content $c$ and its
   primitive part $p$
   ([scaling and primitive parts](#scaling-and-primitive-parts-of-sums)):
   $c$ multiplies into the coefficient, and $p$ becomes the item $(p, 1)$. A
   one $(b^{-1})^0$ is set aside. A power $b^k$ with $k \ne 0$ becomes the
   item $(b, k)$, and any other operand $t$, a symbol or a call, the item
   $(t, 1)$. Coefficients are multiplied exactly.
2. **Merging by key.** The key of an item $(b, k)$ is its base $b$ and the
   sign of $k$. Items with equal keys merge by adding their exponents, which
   have one sign, and the sum is checked as an [exponent](#exponents). Items
   of one base whose exponents have opposite signs have different keys and
   are never merged: $x^2 x^{-1}$ and $x x^{-1}$ keep both factors, while
   $x^{-1} x^{-2} = x^{-3}$. A sum is compared by its primitive part, so
   $(2x + 2y)(y + x) = 2 (x + y)^2$.
3. **Factors.** Each key gives one factor: the base for the exponent 1, and
   the power $b^k$ otherwise.
4. **Zero coefficient.** When the coefficient is 0, the product is the zero
   witness $0 \cdot \prod_{b \in \max N} b^{-1}$ over the factors and the
   ones that were set aside, or the number 0 when that set is empty
   ([negative exponents](#negative-exponents-and-witnesses)).
5. **Ones.** Otherwise, the bases that the ones set aside hold with a
   negative exponent and that the factors do not hold with one are kept by
   the ones $(b^{-1})^0$ of their maximal elements, which join the factors;
   so a one whose base the factors hold is dropped, and $N$ of the product
   keeps $N$ of every one.
6. **Order.** The factors are sorted by key: by base in the total order, and
   for one base the key with a nonnegative exponent first. A one
   $(b^{-1})^0$ has the key of its base $b^{-1}$ with a nonnegative exponent.
7. **Assembly.** Without factors the product is its coefficient, a number;
   with the coefficient 1 and one factor it is that factor; with another
   coefficient and one factor that is a sum, it is that sum scaled by the
   coefficient, so $2 (x + y) = 2x + 2y$; otherwise it is a product node.

### Powers

`Term::power` builds the canonical power $b^k$:

1. The exponent $k$ is checked as an [exponent](#exponents) before anything
   else, and then one unit is charged.
2. A numeric base is evaluated strictly by `Rational::power`: $0^0 = 1$, a
   negative power of 0 fails with `DivisionByZero`, and the bound on the
   bits of the result is checked before the value is computed, as the
   [exact numbers](../numbers/contract.md#checks-and-charges) state.
3. The exponent 1 gives the base.
4. The exponent 0 gives the number 1 when the base holds no power with a
   negative exponent, and otherwise the ones $(b^{-1})^0$ of the elements $b$
   of $\max N(\mathrm{base})$: the one itself for a single element, and
   otherwise the product of the ones with the coefficient 1.
5. An integer power distributes over a product:
   $(c \prod f)^k = c^k \prod f^k$, with $c^k$ computed strictly, so a
   product with the coefficient 0 raised to a negative power fails with
   `DivisionByZero`; each $f^k$ follows rule 7, and the canonical product of
   the results is built.
6. A sum $s = c \cdot p$, with its content $c$ and its primitive part $p$,
   gives $c^k p^k$: $c^k$, which is not 0, is computed strictly, $p^k$
   follows rule 7, and their product is assembled as rule 7 of
   [products](#products) states, which is $p^k$ alone when $c^k = 1$. A sum
   whose content is 1 is its own primitive part. So
   $(2x + 2y)^2 = 4 (x + y)^2$ and $(1 - x)^{-1} = -(x - 1)^{-1}$.
7. For any other base, while the base is itself a power $b^j$ for which the
   merge condition holds, $jk \lt 0$, or $j, k \ge 0$, or $j = 0$, the power
   $(b^j)^k$ becomes $b^{jk}$, and the product $jk$ is checked as an
   exponent. Then the exponent 1 gives the base, the exponent 0 the ones of
   rule 4, and any other exponent a power node.
8. A power of a sum is not expanded.

So $(x^{-1})^2 = x^{-2}$, $(x^2)^{-1} = x^{-2}$ and $(x^2)^3 = x^6$, while
$(x^{-1})^{-1}$ and $(x^{-2})^{-3}$ stay as written; a power of a power merges
only where no base that occurs with a negative exponent is lost. Every integer
power of a one $(b^{-1})^0$ is the one itself, so
$((x^{-1})^0)^{-1} = (x^{-1})^0$.

### Sums

`Term::sum` builds the canonical sum of its operands; `subtract` adds the
negation of its operand, which
[scales](#scaling-and-primitive-parts-of-sums) a sum by $-1$.

1. **Flattening.** The operands are taken from a work list in order. A number
   adds into the constant, which starts at 0. A sum adds its constant and puts
   its monomials on the work list. A product $c \cdot F$ becomes the monomial
   of the coefficient $c$ and the core $F$ without its coefficient: the
   product itself when $c = 1$, its only factor when it has one, which is
   never a sum, and otherwise the product of its factors with the
   coefficient 1. Any other term $t$, a symbol, a call or a power, becomes
   the monomial $1 \cdot t$. Constants and coefficients are added exactly.
   No core is therefore a sum.
2. **Merging.** The monomials are sorted by core in the total order, and
   monomials with equal cores add their coefficients.
3. **Cancellation.** Monomials whose coefficient became 0 are removed. The
   bases that they hold with a negative exponent and that no remaining core
   holds with one are kept in a single witness monomial with the coefficient
   0, $0 \cdot \prod_b b^{-1}$ over the maximal elements of those bases, at
   its place among the cores; its core is $b^{-1}$ for one base and the
   product of the reciprocals with the coefficient 1 otherwise.
4. **Assembly.** Without monomials and with the constant 0, the sum is the
   zero witness of the bases of rule 3, or the number 0 when there are none.
   Without monomials it is its constant, a number. With the constant 0 and
   one monomial it is that monomial: its core for the coefficient 1, and
   otherwise the product of the coefficient and the factors of the core.
   Otherwise it is a sum node.

### Scaling and primitive parts of sums

A number does not stay in front of a sum, and a sum that is a factor or a
base is taken in one form, so that scaled copies of one sum merge whatever
their grouping.

- **Scaling.** A number $c$ other than 0 and 1 times a sum $s$ is the sum
  whose constant and coefficients are those of $s$ multiplied by $c$, over
  the cores of $s$ in their order. It is the product of $c$ and $s$, the
  negation of $s$ for $c = -1$, and the quotient of $s$ by $1/c$:
  $2 (x + y) = 2x + 2y$ and $-(x + y) = -x - y$. The cores, their order and
  the witness monomial of $s$ stay, and no other coefficient becomes 0, so
  the scaled sum is canonical as it is built. $1 \cdot s$ is $s$, and
  $0 \cdot s$ follows the witnesses: it is the zero witness of
  $\max N(s)$.
- **Content.** The content of a sum is the coefficient of its first
  monomial, in the order of the cores, whose coefficient is not 0, or its
  constant when its only monomial is the witness monomial. A sum has at
  least two parts and at most one monomial with the coefficient 0, so the
  content is never 0.
- **Primitive part.** The primitive part of a sum $s$ with the content $c$
  is $p = s / c$, the scaling of $s$ by $1/c$, whose content is 1; a sum
  whose content is 1 is its own primitive part. Only the division of
  rationals is used, never a greatest common divisor. $p$ has the cores of
  $s$, so $N(p) = N(s)$, and $p$ is 0 exactly where $s$ is.
- **Sums as factors and bases.** A sum that is a factor of a product or the
  base of a power is taken as $s = c \cdot p$: $c$ joins the coefficient of
  the product, and $s^k = c^k p^k$, by rule 1 of [products](#products) and
  rule 6 of [powers](#powers). So $(2x + 2y) z = 2 (x + y) z$,
  $(2x + 2y)^2 = 4 (x + y)^2$, $(1 - x)^{-1} = -(x - 1)^{-1}$ and
  $(3x + 2y) z = 3 (x + \frac{2}{3} y) z$, written `2*z*(x + y)`,
  `4*(x + y)^2`, `-(-1 + x)^(-1)` and `3*z*(x + 2/3*y)`. The exponent 0 of
  rule 4 of powers agrees: $c^0 = 1$, and $\max N(p) = \max N(s)$.

So with $s = x + y$, $a = 2s$ and $b = -s$, the sums $a + b + b$ and
$(a + b) + b$ are both 0, $(a + b) + (a + b)$ and $a + b + a + b$ are both
$2x + 2y$, and $s - s$ is 0, whose power $-1$ fails with `DivisionByZero`.

### Canonical shape

Every node of every term that the constructors return satisfies these
invariants:

- a number holds a canonical `Rational`, and a symbol a valid name that is
  not reserved;
- a power $b^k$ has a base that is neither a number nor a product, a base
  that is a sum is primitive, and the exponent is not 1; the exponent is 0
  only in a one $(c^{-1})^0$; and when the base is a power $c^j$, the merge
  condition of rule 7 of [powers](#powers) does not hold for $j$ and $k$;
- a product has at least one factor, and a single factor only with a
  coefficient other than 1 and only when that factor is not a sum; no factor
  is a number or a product, and a factor that is a sum is primitive; the
  keys of the factors increase strictly in the order of rule 6 of
  [products](#products); with the coefficient 0, every factor is a
  reciprocal $b^{-1}$, and no base occurs with a negative exponent inside
  another; with any other coefficient, no other factor holds the base of a
  one with a negative exponent, and no base of a one occurs with a negative
  exponent inside the base of another one;
- a sum has at least two parts, its monomials and its constant when that is
  not 0; its cores increase strictly in the total order; no core is a number
  or a sum, and a core that is a product has the coefficient 1; and at most
  one monomial has the coefficient 0, the witness monomial of rule 3 of
  [sums](#sums), whose core is a reciprocal or a product of reciprocals with
  the coefficient 1, whose bases no other core holds with a negative
  exponent, and none of whose bases occurs with a negative exponent inside
  another of them.

### Strict numeric evaluation

Numeric subterms are evaluated when they are built, so an invalid numeric
subterm fails at once and cannot be absorbed by the term around it:

- $0^0 = 1$;
- $0^{-1}$ fails with `DivisionByZero`, and so does every negative power of
  zero, and every negative power of a product with the coefficient 0;
- $1/0$ fails with `DivisionByZero` when it is built, since `divide` raises
  the divisor to the power $-1$ first, so $0 \cdot (1/0)$ and $(1/0)^0$ fail
  with it, and so does a quotient by a product with the coefficient 0, such
  as $x / (0 \cdot x^{-1})$;
- under the default limits, $x / x^{2^{32}}$ fails with `ResourceLimit`
  naming `max_exponent`, with the amount $2^{32}$, when $x^{2^{32}}$ is
  built: the exponent is checked before any charge and before any large
  value is built.

### Negative exponents and witnesses

Write $N(t)$ for the set of bases that occur with a negative exponent in a
term $t$: the bases $b$ of every power $b^k$ with $k \lt 0$ in $t$, nested
ones included. A base that is a sum is taken by its
[primitive part](#scaling-and-primitive-parts-of-sums), also inside the
witnesses: a power of a sum $s = c \cdot p$ raises $p$, so every base of a
canonical term that is a sum is primitive, and since $c \ne 0$, $s$ and $p$
are 0 at the same points. Write $\max N(t)$ for those elements of $N(t)$
that do not themselves occur with a negative exponent inside another
element. Every element of $N(t)$ outside $\max N(t)$ occurs with a negative
exponent inside a maximal one, so a term that holds the maximal elements
holds all of $N(t)$.

- **The invariant.** Canonicalization never shrinks this set: for every
  constructor, $N$ of each operand is contained in $N$ of the result,

  ```math
  N(\mathrm{input}) \subseteq N(\mathrm{output})
  ```

  with a base of an operand that is a sum taken by its primitive part, as
  the operands of a constructor already hold it, and `has_negative_power()`
  is true exactly when $N$ of the term is not empty.
- **Introduced negative powers.** The negative power that a constructor
  introduces is kept as well: the term that `power` returns for an exponent
  $k \lt 0$, or that `divide` returns, which raises its divisor to the power
  $-1$, is undefined wherever the base or the divisor $b$ is 0, and where
  $b$ is the number 0 or a product with the coefficient 0 the construction
  fails with `DivisionByZero` instead. A numeric $b$ is evaluated strictly.
  For any other $b$, $N$ of the result holds $b$ when $b$ is a symbol, a
  call or a power $c^j$ with $j \lt 0$; the primitive part of $b$ when $b$
  is a sum, which is 0 exactly where $b$ is; $c$ when $b = c^j$ with
  $j \gt 0$; and, for a product $b$, these bases for each of its factors, of
  which a one contributes none. A one $(c^{-1})^0$, which is never 0, raised
  to $k$ is the one itself. With the invariant, a canonical form therefore
  never hides a point where its input is undefined.
- **Three witnesses.** Where a simplification would lose a base, the term
  keeps a witness instead:
  - a product whose coefficient is 0 is $0 \cdot \prod_{b \in \max N} b^{-1}$,
    and the number 0 when the set is empty;
  - when $N(t)$ is not empty, $t^0$ is $\prod_{b \in \max N(t)} (b^{-1})^0$,
    a product of ones;
  - in a sum, monomials that cancel to zero leave the bases that the
    remaining monomials do not cover in a single witness monomial with the
    coefficient 0.
- **Minimal witnesses.** A witness names the maximal elements of the bases it
  keeps, and a one in a product is dropped when the other factors already
  hold its base with a negative exponent. The maximal elements are the bases
  without the inner ones, those that occur with a negative exponent inside
  the base of a negative power of the same operands. Of the bases that the
  other factors or the remaining monomials do not hold, the same test keeps
  the maximal ones, since $N$ of a term holds every base inside each of its
  elements.
- **Powers of witnesses.** A one $(b^{-1})^0$ raised to any integer power is
  the one itself.

So $x^2 x^{-1}$, $x x^{-1}$, $(x^{-1})^{-1}$, $0 \cdot x^{-1}$ and
$(x^{-1})^0$ each stay as written, $x^{-1} - x^{-1} = 0 \cdot x^{-1}$,
$5 + x^{-1} - x^{-1} = 5 + 0 \cdot x^{-1}$ and $x^{-1} x^{-2} = x^{-3}$; a
base that is a sum is kept by its primitive part,
$0 \cdot (2x + 2y)^{-1} = 0 \cdot (x + y)^{-1}$ and
$(2x + 2y)^{-1} (x + y) = \frac{1}{2} (x + y) (x + y)^{-1}$. Removing
negative exponents under conditions is an explicit operation of a later
release, never part of a constructor.

`negative_bases()` returns $N$ of the term, sorted in the total order and
without repetitions.

### Exponents

An exponent is an `i64`. Every exponent that the term core takes or computes,
the argument of `power`, the sum of the exponents of one key in a product,
the product of two exponents in a power of a power and an integer that the
parser reads as the exponent of a power, is checked against
`max_exponent` and against the width of `i64`: the effective bound is the
smaller of `max_exponent` and $2^{63} - 1$, and an exponent of a larger
magnitude fails with `ResourceLimit` naming `max_exponent`, with that
effective value as `allowed`, as the
[errors](../errors/contract.md#bounds-set-by-a-machine-width) state for a
bound set by a machine width. Sums and products of exponents are computed
exactly in `i128` before the check, and an exponent is checked before it is
used, without a charge. So `i64::MIN` is never an exponent, and the negation
of an exponent never overflows. An integer that the parser reads as an
exponent and whose magnitude does not fit in a `u64` fails with the amount
`LimitAmount::Bound(u64::MAX)`, and its error carries the span that the parser
gives. Under the default limits an exponent has a magnitude of at most 4096.

### Calls and reserved names

- **Calls.** Function calls arrive in release 0.2, and their shape and place
  are fixed now so that the canonical forms of the terms of 0.1 do not change
  when they arrive. A call is `Call(Head { name, class }, args)`: its class
  is `Registered` or `Formal` and `#[non_exhaustive]`, and its arguments are
  canonical terms in their given order, not sorted. Calls are ordered by head
  name, not by a registry index, so registering a function never reorders
  existing calls. A call is an atom of sums, products and powers: it can be a
  base or a core, merges as one, and is never expanded. No constructor of
  this release builds a call, so the canonical form and the order of a
  call-free term depend on no rule about calls. Only test code builds a call
  node, through `reserved_call`, which counts its head name and 4 bytes per
  argument; the cost formula of calls is fixed when they arrive.
- **Reserved names.** `pi`, `i` and `undefined` are reserved for the
  constants of a later release. `Term::symbol` rejects them with
  `Fault(Unsupported)` and the span of the whole name, after the form of the
  name has been checked and before any charge, so an input accepted today
  keeps its meaning and its canonical form when the constants arrive;
  otherwise $i \cdot i$ would change from $i^2$ to $-1$, and the rank of
  `pi` from 2 to 1. Names that only resemble them, such as `Pi`, `ii` or
  `pi2`, are symbols.

### Symbol names

A symbol name is an ASCII letter or `_`, followed by ASCII letters, digits and
`_`: the identifiers of the input syntax. Any other name fails with
`Fault(Syntax)`, with the span of its first character that the form does not
allow (the whole character, also when it is not ASCII), or with the empty span
at 0 for the empty name. The name is checked before any charge; an accepted
name is then checked as a node, and its node is charged one unit and one more
per byte of the name.

### Size, depth and storage

- **Size.** The tree size of a term is its number of nodes, a shared subterm
  counted once for each occurrence. Coefficients, constants and exponents
  stored in a node add no nodes.
- **Depth.** A number and a symbol have the depth 1, and any other node one
  more than the largest depth of its children.
- **Logical bytes.** The bytes of a term are those of its canonical binary
  rendering, the term formula of the
  [architecture](../../architecture.md#storage-bytes), which this contract
  fixes. Write $\lvert x \rvert$ for the bit length of an integer $x$,
  $\mathrm{rb}(q) = \lvert n \rvert + \lvert d \rvert + 3$ for the bytes of
  a rational $q = n/d$, and $\ell$ for the bytes of a symbol name. A number
  costs $\mathrm{rb}$ of its value and a symbol $\ell$. A power costs its
  base, its exponent written as the rational $k/1$, $\lvert k \rvert + 4$
  bytes, and 4 for the operator. A product of $m$ factors costs its factors
  and $4(m - 1)$ with the coefficient 1, and otherwise its factors,
  $\mathrm{rb}$ of the coefficient and $4m$. A sum costs its cores,
  $\mathrm{rb}(c) + 4$ for each coefficient $c$ other than 1, $\mathrm{rb}$
  of the constant when it is not 0, and 4 for each of the operators between
  its parts. So $c x^k$ with $c \ne 1$ and $k \ge 2$ costs
  $\mathrm{rb}(c) + \ell + \lvert k \rvert + 12$ bytes, and $xy$ costs
  $\ell_x + \ell_y + 4$. Shared subterms count once per occurrence, as for
  the size.
- **Cost.** `StorageCost` for a term is its tree size in nodes and its
  logical bytes, both cached in its node. The formula becomes part of the
  compatibility contract with the release tag of the component; changing it
  changes which limit is reached first, so it is a change of the answer
  vectors, made on purpose.
- **Checks before every node.** Before a node is allocated, its depth is
  compared with `max_depth`, and an excess fails with
  `LimitId::Field(Depth)` and no scope. Then its cost, the tree size and the
  logical bytes of the new term, is checked with
  `check_storage(cost, LimitScope::Value)`: the costs of the open frames,
  the reserved temporaries and the new term together must fit `max_nodes` and
  `max_storage_bytes`, and an excess fails with `LimitId::Field(Nodes)` or
  `LimitId::Field(StorageBytes)` and the scope `Value`, with `Nodes` when both
  are exceeded and `LimitAmount::Bound(u64::MAX)` for a total that does not
  fit in a `u64`. Only then is the node charged and its `Rc` allocated, so a
  rejected node charges nothing and allocates no node; the value, the
  children and the coefficients that its caller computed before the checks
  are dropped with the error. Every node is checked, the intermediate ones
  too: a core, a reciprocal, a one or the primitive part of a sum built along
  the way, and a scaled sum, whose coefficients are each checked against
  `max_integer_bits` when they are computed. The size of one
  term is a special case of the retained total; there is no separate limit
  on a single term.
- **Receiving limits.** A term built under one context and used under
  another is checked against the receiving context: its numbers against
  `max_integer_bits` where they take part in arithmetic, in a comparison or in
  a display, and its tree size, its bytes and its depth as a part of every
  node built on it.

### Charges

Every step of the term core is charged to the context, including the scans
of monomials and the collection loops, which are charged per monomial or item
that they pass.
The amounts depend only on the operands, never on the limits, the remaining
work or the sharing of nodes, so the same construction charges the same work
in every run.

| Step | Charge |
| --- | --- |
| A node, after its checks | 1, and 1 per child |
| A symbol node, after its checks | 1, and 1 per byte of the name |
| A number node, after the bit check of its value | 1 |
| An operand taken from the work list of a sum or a product | 1 |
| A sum of two constants or coefficients | as `Rational::add`; with an operand 0, the bits of the other are checked, then 1 |
| A product of two coefficients | as `Rational::multiply`; with an operand 1, the bits of the other are checked, then 1; with an operand $-1$, as `Rational::negate` |
| Sorting items | each comparison, and 1 per item placed in each pass of a bottom-up merge sort |
| Merging sorted items | 1 per item, the comparison with the last item kept, and for monomials with equal cores the sum of their coefficients |
| The removal of zero monomials, the collection of the remaining cores when a cancelled monomial holds a negative power, and the split of the monomials into coefficients and cores | 1 per monomial each |
| The factors of the merged items, and the keys of the factors when ones join them | 1 per factor each |
| The content of a sum that is a factor or a base | 1 |
| The primitive part of a sum whose content $c$ is not 1 | the inverse $1/c$ as `Rational::inverse`, then the scaling of the sum by $1/c$ |
| The scaling of a sum by a number $c$ | the product of $c$ and the constant, then for each monomial 1 and the product of $c$ and its coefficient, each as a product of two coefficients |
| A sum taken as a factor of a product | its content, its primitive part, then the product of the content and the coefficient |
| A coefficient other than 0 and 1 times a single factor that is a sum | the scaling of the sum by the coefficient, in place of a product node |
| A power | 1 after the exponent check; for a numeric base `Rational::power`; for a product the power of the coefficient and 1 per factor; for a sum its content and its primitive part, and when the content $c$ is not 1, $c^k$ as `Rational::power`; 1 per merge of a power of a power |
| $N$ of a list of terms | 1 per node visited (the roots, and the children of the nodes that hold a negative power), then sorting and merging the bases found; for the maximal bases of a witness, the inner bases, those found inside the base of a negative power, are collected in the same traversal, sorted and merged as well, and removed by a set difference |
| A set difference of sorted bases | 1 per element, and the comparisons of a binary search |
| A comparison | 1 per step, where the cursor that walks the children or the monomials of two nodes takes one step at each common position it reaches and one past the last; 1 per byte of the shorter of two compared names; and `Rational::compare` for two numbers |
| A display | 1 per step, and `charge_output` of each piece of text before it is written: 1 output byte and 1 unit per byte |

The exponent and name checks and the accessors charge nothing. Drop is not
charged: it has no context, and its work is bounded by the nodes that were
built and charged. When a charge fails, the construction stops with the
request failure of the charge, and nothing that it built is returned.

### Traversal and drop

- **No native recursion.** Comparison, display and the collection of
  negative-exponent bases are each one loop over a stack on the heap. Their
  frames hold owned terms, whose clones only increment a count, and copied
  scalars, never borrowed references; a field inside a node, such as a
  coefficient or a head, is read when the frame that holds both nodes is
  taken from the stack. A comparison walks the children or the monomials of
  two nodes with a cursor frame that pushes one pair at a time and then the
  cursor of the next position, so every step does a bounded amount of work
  and a comparison that a pair decides never touches the pairs after it.
  The constructors keep their work lists on the heap and read the cached
  values of their operands, and no function of the component calls itself,
  directly or through another.
- **Drop.** `Drop` for a node moves its children onto a stack of its own and
  releases them one at a time with `Rc::try_unwrap`: a child that the node
  owns alone gives its children to the stack before it is freed, and a
  shared child only loses a count.
- **Depth.** The native stack use of every operation of the component
  therefore does not grow with the depth of a term
  ([convention 15](../../conventions/public-api.md#15-depth)); a term is
  rejected by `max_depth` only when a node is built.
- **Debug.** `Debug` for a term is shallow: it shows the kind, the value of a
  number, the name of a symbol or the exponent of a power, the number of
  children, the size and the depth, and never the children.

### Display

`display()` writes the text of a term in this grammar, with parentheses only
where the grammar needs them:

- **Number.** Its numerator in decimal, with `-` when it is negative, and `/`
  and its denominator unless that is 1: `-3/4`, `5`, `0`.
- **Symbol.** Its name.
- **Power.** Its base, `^` and its exponent. The base is in parentheses unless
  it is a symbol or a call. A nonnegative exponent is its decimal digits, and
  a negative exponent is `(-`, its magnitude and `)`: `x^2`, `x^(-1)`,
  `(x + y)^(-2)`, `(x^(-1))^0`, `(-1 + x)^(-1)`.
- **Product.** The prefix of its coefficient, which is nothing for 1, `-` for
  $-1$ and otherwise the number and `*`, then its factors in their stored
  order joined by `*`, each sum among them in parentheses: `x*y`, `-x*y`,
  `-2*x`, `1/2*x^(-1)*y^(-1)`, `-z*(x + y)`, `2*z*(x + y)`,
  `3*z*(x + 2/3*y)`, `4*(x + y)^2`, `0*x^(-1)`.
- **Sum.** Its constant when that is not 0, then its monomials in their
  stored order. Each monomial is written as a separator, then the magnitude of
  its coefficient and `*` when that magnitude is not 1, then its core, which
  is never a sum. The separator is ` - ` for a negative coefficient and
  ` + ` otherwise, the coefficient 0 of a witness monomial included; the
  first part of the text, a monomial when the constant is 0, has no separator
  and only `-` for a negative coefficient: `2 + x + y`, `1 - x`, `-x + y`,
  `-2*x - y`, `2*x + 2*y`, `x - z*(x + y)`, `5 + 0*x^(-1)`.
- **Call**, reserved: its name, `(`, its arguments joined by `, `, and `)`.

The order of the factors and of the monomials is their stored, canonical
order, so the constant of a sum comes first and its monomials follow in the
total order of their cores. The text is ASCII and depends only on the term,
which by [uniqueness](#uniqueness) is the same for every grouping and every
order of the same operands: the text is byte for byte the same for every way
of building the term, in every run and on every host, so $2 (x + y)$,
$(x + y) + (x + y)$ and $(2x + y) + y$ are all written `2*x + 2*y`. As
[convention 10](../../conventions/public-api.md#10-bounded-output) asks,
`display()` takes the context, charges one unit per step and charges each
piece of text with `charge_output` before it writes it; when a charge fails,
it returns the error and no text. There is no `impl Display` for a term.

## Requirements

The earlier implementation has no requirement identifiers for its terms, so
the requirements of this component are named after the invariants that they
state; the six canonical-form invariants come first. Tests are in
`tests/terms.rs` unless the entry names `tests/term_properties.rs`,
`src/term/tests.rs` or `src/term/exponent.rs`. Each canonical-form invariant
also has a property test of 1,000 cases in `tests/term_properties.rs`, as
[testing obligation 2](#testing-obligations) states, which its evidence
names.

### Uniqueness

Every canonical term has one form: `compare` gives `Equal` for two canonical
terms exactly when their structure is equal, and the constructors give the
same canonical term, with the same display bytes, for every grouping and every
order of the same operands of a sum or a product. A number distributes over a
sum, and a sum that is a factor or a base is taken by its primitive part, so
scaled copies of one sum merge in every grouping: with $s = x + y$, $a = 2s$
and $b = -s$, the sums $a + b + b$ and $(a + b) + b$ are both 0, and
$(a + b) + (a + b)$ and $a + b + a + b$ are both $2x + 2y$; and $s - s$ is
0, whose power $-1$ fails with `DivisionByZero`. With opposite signs never
merged, $(x \cdot x^{-2}) \cdot x^2$ and $x \cdot (x^{-2} \cdot x^2)$ are both
$x^3 x^{-2}$.

- **Implemented here.** The work lists, the merging by key and by core, and
  the sorting of `src/term/product.rs` and `src/term/sum.rs`, with the
  scaling and the primitive parts of sums in `src/term/sum.rs`, which
  `src/term/product.rs` and `src/term/power.rs` use.
- **Evidence.** Negative example:
  `uniqueness_scaled_copies_of_one_sum_give_one_form_in_every_grouping`.
  Property: `uniqueness_every_order_and_grouping_of_the_operands_gives_one_term`
  in `tests/term_properties.rs`. Also
  `a_sum_minus_itself_is_zero_and_has_no_reciprocal`,
  `uniqueness_every_grouping_of_opposite_signs_gives_one_form`,
  `sums_as_factors_and_bases_are_primitive`,
  `construction_order_does_not_change_the_display_bytes`,
  `sums_built_in_different_orders_merge_as_bases_and_cores` and, in
  `src/term/tests.rs`, `equal_terms_built_apart_are_separate_nodes`.

### Idempotence

Rebuilding a canonical term through the constructors from its parts, as the
accessors give them, gives a structurally equal term with the same display
bytes: every node satisfies the [canonical shape](#canonical-shape), and in
particular no monomial core of a sum is a sum, every sum that is a factor or
a base is primitive, and a content that cancels against a coefficient leaves
no product with the coefficient 1: $\frac{1}{2} (2x + 2y) = x + y$ and
$(1 - x)^2 = (x - 1)^2$.

- **Implemented here.** The scaling and the primitive parts of sums in
  `src/term/sum.rs`, and the assembly of every constructor.
- **Evidence.** Negative example:
  `idempotence_a_content_that_cancels_leaves_no_product`. Property:
  `idempotence_rebuilding_a_term_from_its_parts_gives_the_term` in
  `tests/term_properties.rs`. Also, in `src/term/tests.rs`,
  `sample_terms_keep_the_local_rules_of_the_canonical_form` and
  `scaling_keeps_the_cores_and_the_primitive_part_has_the_content_1`.

### Order of terms in sums and products

The monomials of a sum are sorted by core and the factors of a product by key,
both in the [total order](#kinds-and-the-total-order), whatever the order of
the operands; the order ranks numbers, symbols, calls, powers, products and
sums in this order.

- **Implemented here.** `src/term/order.rs` and the merge sort of
  `src/term/sort.rs`.
- **Evidence.** Negative example: `order_sums_and_products_sort_their_terms`,
  which also orders symbols whose names are prefixes of each other. Property:
  `order_of_terms_factors_and_monomials_increase_strictly` in
  `tests/term_properties.rs`. Also, in `src/term/tests.rs`,
  `calls_sort_after_symbols_and_before_powers` and
  `calls_order_by_head_name_class_arguments_and_count`.

### Merging of like terms and coefficients

Numbers multiply into one coefficient and add into one constant, exactly;
monomials with equal cores add their coefficients; factors with equal keys add
their exponents. Cores and bases are compared by structure, never by
identity, and a sum among the factors by its primitive part, so
$2 z (x + y) + 3 z (y + x) = 5 z (x + y)$ and
$(2x + 2y)(y + x) = 2 (x + y)^2$.

- **Implemented here.** The merging steps of `src/term/product.rs` and
  `src/term/sum.rs`.
- **Evidence.** Negative example: `merging_like_terms_and_coefficients`.
  Property: `merging_leaves_no_like_terms_and_keeps_the_value` in
  `tests/term_properties.rs`. Also
  `a_power_of_a_product_leaves_no_nested_product_and_no_repeated_key` and, in
  `src/term/tests.rs`, `calls_are_atoms_of_sums_products_and_powers`.

### Elimination of 0 and 1

A summand 0, a factor 1 and the exponent 1 disappear; the empty sum is 0 and
the empty product 1; a sum or a product left with one part is that part; a
product with the coefficient 0 and a sum of cancelled monomials are 0, and
$t^0$ is 1, unless a base that occurs with a negative exponent needs a
witness.

- **Implemented here.** The assembly of products and sums and the rules of
  the exponents 0 and 1 in `src/term/power.rs`.
- **Evidence.** Negative example: `elimination_of_zero_and_one`. Property:
  `elimination_no_zero_and_no_one_is_left_but_a_witness` in
  `tests/term_properties.rs`. Also
  `a_sum_minus_itself_is_zero_and_has_no_reciprocal`.

### Integer powers and the negative-exponent invariant

Powers follow the rules of [powers](#powers), and every constructor keeps
$N(\mathrm{input}) \subseteq N(\mathrm{output})$, a base that is a sum taken
by its primitive part, with the minimal witnesses of
[negative exponents](#negative-exponents-and-witnesses).

- **Implemented here.** `src/term/power.rs`, `src/term/exponent.rs` and
  `src/term/witness.rs`, with the witnesses of products and sums.
- **Evidence.** Negative example: `integer_powers_keep_every_negative_base`.
  Properties, in `tests/term_properties.rs`:
  `integer_powers_merge_distribute_and_keep_their_values` and, as
  [testing obligation 3](#testing-obligations) asks,
  `negative_exponents_every_constructor_keeps_the_negative_bases_of_its_operands`.
  Also `witnesses_keep_only_the_maximal_bases`,
  `witnesses_keep_a_sum_base_by_its_primitive_part`,
  `sums_as_factors_and_bases_are_primitive`,
  `negation_difference_and_quotient_are_canonical`,
  `exponents_beyond_the_width_of_i64_are_resource_limits` and, in
  `src/term/exponent.rs`, `the_merge_condition_never_hides_a_negative_exponent`,
  `magnitudes_cover_the_whole_range_of_i64` and
  `integers_become_exponents_under_the_same_check`.

### Strict evaluation of numbers

The rules of [strict numeric evaluation](#strict-numeric-evaluation).

- **Implemented here.** `src/term/power.rs` with `Rational::power`, and
  `Term::divide`.
- **Evidence.** `zero_times_one_over_zero_is_division_by_zero`,
  `one_over_zero_to_the_zero_is_division_by_zero`,
  `zero_to_the_minus_one_is_division_by_zero`, `zero_to_the_zero_is_one` and
  `x_over_x_to_the_two_to_the_32_exceeds_max_exponent`. Also
  `a_sum_minus_itself_is_zero_and_has_no_reciprocal`.

### Accounting under the request context

Every step is charged as [charges](#charges) state, an exhausted budget ends a
construction with `ResourceLimit` naming `max_work`, every node is checked
before it is allocated as [size, depth and storage](#size-depth-and-storage)
state, and a broken internal invariant is a `Fault(Internal)`, never a panic
([convention 12](../../conventions/public-api.md#12-no-panic)).

- **Implemented here.** `src/term/node.rs` and every charge of the
  component.
- **Evidence.** `an_exhausted_work_budget_is_a_resource_limit`,
  `nodes_storage_bytes_and_depth_are_checked_before_a_node_is_built`,
  `shared_subterms_count_once_per_occurrence_against_max_nodes`,
  `scaled_sums_and_primitive_parts_are_checked_before_they_are_built`,
  `the_storage_formula_of_terms`, `terms_are_checked_against_the_receiving_limits`,
  `numbers_of_max_integer_bits_pass_through_sums_and_products`,
  `constructions_comparisons_and_displays_charge_fixed_amounts`,
  `construction_steps_charge_the_amounts_of_the_charge_table`,
  `scaling_and_primitive_parts_charge_the_amounts_of_the_charge_table`,
  `a_display_beyond_max_output_bytes_returns_no_text` and, in
  `src/term/tests.rs`, `cached_measures_match_a_recursive_count`,
  `the_cost_of_a_call_counts_its_name_and_arguments` and
  `a_broken_invariant_is_an_internal_fault`.

### Depth and drop

Terms of any depth that the limits admit are built, compared, displayed and
dropped with a native stack that does not grow with their depth.

- **Implemented here.** The loops of `src/term/order.rs`,
  `src/term/display.rs` and `src/term/witness.rs`, and `Drop` in
  `src/term/node.rs`.
- **Evidence.** `depth_100000_terms_build_compare_display_and_drop_on_a_2_mib_stack`,
  with `max_depth` raised above the tested depth, and
  `dropping_a_term_keeps_its_shared_subterms` in `src/term/tests.rs`.

### Deterministic display

The text of a term follows the [display](#display) grammar and is the same,
byte for byte, for every way of building the term and in every run.

- **Implemented here.** `src/term/display.rs`.
- **Evidence.** `display_bytes_are_the_same_in_two_runs`,
  `construction_order_does_not_change_the_display_bytes` and
  `the_display_follows_its_grammar`.

### Symbols and reserved names

Symbol names follow the rule of [symbol names](#symbol-names), and the
reserved names fail as [calls and reserved names](#calls-and-reserved-names)
state.

- **Implemented here.** `src/term/symbol.rs`.
- **Evidence.** `reserved_names_are_unsupported` and
  `symbol_names_are_identifiers`.

## Defects of the earlier implementation

The terms of the earlier implementation had two recorded defects that the
term core does not have. Their recorded examples use roots, which are function
calls of a later release, so the tests here state the same defects with
integer powers.

- **Normal forms of products.** The product builder raised each collected base
  to its exponent and kept the power that this gave without collecting again,
  so a product could hold a nested product or two equal operands
  (`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:docs/domains/cross-cutting/rewriting/contract.md:958`).
  Here the factors of a power of a product return to the merging of the
  product: $x (xy)^2 = x^3 y^2$, with no nested product and no two factors of
  one key (`a_power_of_a_product_leaves_no_nested_product_and_no_repeated_key`).
- **Order of sums in the expansion.** The expansion of function expressions
  did not order a sum that served as a base or a core, so equal products did
  not cancel
  (`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:src/symbolic/functions/expansion.rs:199`).
  Here sums built in different orders are equal and merge as bases and as
  cores: $(x + y)^2 (y + x)^3 = (x + y)^5$ and $(x + y) z - z (y + x) = 0$
  (`sums_built_in_different_orders_merge_as_bases_and_cores`).

## Testing obligations

1. **Negative examples.** Each of the six canonical-form invariants has a test
   with a fixed input that an implementation which breaks the invariant gets
   wrong, as each requirement names it.
2. **Properties.** Each of the six canonical-form invariants has a property
   test of 1,000 cases from a fixed seed, over terms from a generator written
   in the test, through the public interface only: the first six tests of
   `tests/term_properties.rs`, with the seeds `0x5EED_0000_0000_0001` to
   `0x5EED_0000_0000_0006`. The generator writes several scaled copies of one
   sum $s$ among the operands of a sum, such as $[2s, -s, -s]$ and
   $[2s, -s, 2s, -s]$.
3. **The negative-exponent invariant.** A second property test of 1,000 cases
   from a fixed seed,
   `negative_exponents_every_constructor_keeps_the_negative_bases_of_its_operands`
   in `tests/term_properties.rs` with the seed `0x5EED_0000_0000_0007`,
   checks that $N$ of every operand is contained in $N$ of the result, for
   sums, products, powers, negations, differences and quotients, with a
   generator that covers the shapes $x^2 \cdot x^{-1}$, $x \cdot x^{-1}$,
   $0 \cdot x^{-1}$ and $(x^{-1})^0$, each in at least 100 inputs. It also
   checks the negative powers that the input introduces: every base of a
   negative power and every divisor of the input whose canonical form is a
   symbol, or a sum by its primitive part, is in $N$ of the result, and at
   sample points where the input is undefined, the result is undefined too.
4. **Strict evaluation.** $0 \cdot (1/0)$, $(1/0)^0$ and $0^{-1}$ fail with
   `DivisionByZero`, $0^0 = 1$, and $x / x^{2^{32}}$ fails with
   `ResourceLimit` naming `max_exponent` under the default limits.
5. **Limits.** An exhausted work budget, `max_nodes`, `max_storage_bytes` and
   `max_depth` each fail with their own field, the storage fields with the
   scope `Value`; the open frames and the reserved temporaries count.
6. **Depth.** Two chains of depth at least 100,000, $t_{i+1} = x t_i + 1$ and
   nested negative powers, are built, compared, displayed and dropped on a
   thread with a stack of 2 MiB, with `max_depth` set above their depth, as
   [convention 15](../../conventions/public-api.md#15-depth) asks.
7. **Display.** The same term built in two runs, and built in different
   orders under associativity and commutativity, has the same display bytes.
8. **Defects.** Each defect of the earlier implementation above has a test.
9. **Work.** Tests assert the charges that this contract fixes, that a
   rejected node charges nothing and that a construction charges the same
   under different limits; they assert no other amount.
10. **No message text.** No test asserts the message of an error; tests
    compare the kind, the span and the exceeded limit.

## Extractability

The canonical forms are planned for tier A2 in release 0.2, so the term core
is written in the provable subset of Rust from its first change, as the
[architecture](../../architecture.md#verification-tiers) requires; no proof
target is registered for it yet, and none of its code has been extracted. The
subset is that of the krepi convention on the provable subset of Rust: the
constructs R1 to R7, the provable design rules 1 to 9 and the loop shapes.

- **Constructs.** No function item is passed as a value (R1), no
  `Iterator::any` (R2) or `Iterator::flatten` (R3) is called, and no closure
  is given to a combinator or an adapter (R4): searches and walks are index
  loops or loops over an explicit stack, and the sort is generic over the
  crate-private trait `SortItem`, whose `&self` methods it calls. A mutable
  borrow of the last merged item is taken by `last_mut` in a `match` whose
  arms both end the function, and no mutable borrow is held across a write to
  another value (R5). The enumerations have names that are unique in kalyx:
  `TermKind`, `TermShape`, `CallClass`, `TermOrderStep`, `TermDisplayStep`,
  `TermDisplayToken` and `SumOperand` (R6). R7 concerns Lean code, which the
  component does not have.
- **Loop shapes.** A function has at most one loop. A function whose loop
  uses `?` leaves before the loop only through `?`, owns no value that needs
  dropping at such a `?` when its loop holds two or more, and has its loop at
  the top level of its body; checks that return early are in loopless
  functions that call the helper with the loop. Slices are walked by index
  loops, work lists by `while let` over `Vec::pop`, and the merges of a power
  of a power by `while let` over a step function called with `?`; the
  content of a sum reads its first two coefficients without a loop; no loop
  condition is a macro.
- **Traversal frames.** The frames of comparison and display,
  `TermOrderStep` and `TermDisplayStep`, and the stacks of the collection of
  bases and of drop hold owned terms and copied scalars; no frame has a
  lifetime parameter.
- **Integer conversions.** Conversions that cannot lose information are `as`
  casts; the magnitude of an `i64` is computed in translated arithmetic by
  `exponent::magnitude`; exponents are summed and multiplied in `i128` and
  converted back with an `as` cast after a bound check. An integer that the
  parser reads as an exponent becomes a `u64` magnitude through
  `Integer::magnitude_u64`, an operation of the exact numbers outside the
  subset, and an `i64` by an `as` cast after the bound check of
  `integer_exponent`. No `unsigned_abs`, `try_from` or `From` conversion
  between machine integers is used.
- **Design rules.** Every check of a node, of an exponent and of a name
  comes before the charge and the allocation (1). Each node is allocated on
  the heap at run time, only after its checks of `max_depth`, `max_nodes` and
  `max_storage_bytes`; the work lists, the children and shape data that a
  constructor prepares for a node, and the stacks of comparison, display and
  the collection of bases are allocated at run time without a check, bounded
  by the operands and by the charged steps that fill them; rules 2 and 3 are
  written for kernels and do not apply. Every loop step is charged or bounded
  by charged steps: a step that pushes the children of a node onto a work
  list or a stack has each of them charged when it is taken, and a
  comparison, which stops at the first pair that differs, takes the pairs of
  children one at a time through its cursor. So `max_work` bounds the work
  of every entry, also where the collection of bases and the witness rules
  take more than linear work in the size of a term, except the check of a
  symbol name, which reads the name before any charge, so a rejected name
  charges nothing (4). The size, the depth, the logical bytes and the
  negative flag are fields of the node (5). The fields of `Term` and of its
  node are private, and a compile-time assertion keeps `Term` from being
  `Send` (6). The only `cfg` is `#[cfg(test)]` on the test modules, one of
  which holds `reserved_call`; the reserved call variant and its class carry
  a lint expectation selected by `cfg_attr`, which changes no shape (7).
  There is no `Cell` or `RefCell`; the count of an `Rc` is visible only to the
  `Rc::try_unwrap` of drop, which a model treats with value semantics (8).
  The library forbids `unsafe` code (9).
- **External declarations.** No code has been extracted, so this list
  follows the records of the qualification of the earlier implementation
  (`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:docs/formal-verification.md:432-434`
  and the Code shapes section at
  `cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:docs/formal-verification.md:1452`).
  An extraction needs `Rc` with `Rc::new`, `Rc::try_unwrap`, its clone and
  its dereference, through a structure model of `Rc` like the one the earlier
  implementation used for `Arc`. Of `Vec` and slices, `pop`, `truncate`,
  `is_empty`, `append`, `std::mem::take` with `Default` for `Vec`, and
  `slice::from_ref` are recorded as external; `push`, indexing and `len` are
  recorded as translated with library models; and `new`, `with_capacity`,
  `extend_from_slice`, `insert`, `clone`, `swap`, `reverse`, `first`, `last`,
  `last_mut`, `get` and the `vec!` macro are not recorded.
  `usize::saturating_mul`, with which the merge sort doubles the width of
  its runs, is recorded as external, while the other machine-integer
  operations of the term core, such as `checked_add`, `checked_mul`,
  `saturating_add` and `saturating_sub` on `u64`, are not. The list also
  needs `str::len` and `str::as_bytes`, which are recorded as external, and
  `Box<str>` from a `&str`, which is not recorded; `==` and `!=` on
  `Ordering`, which are recorded as external, while a `match` on an
  `Ordering` translates; the operations of `Rational` and `Integer`, which
  wrap num-bigint and num-rational; the methods of the context; and
  `Error::new`, which copies its message into a `String`. Every string
  literal of an error message adds a `decide +native` axiom, and no
  qualification case covers the byte-string literals of the reserved names.
  Display and `Debug` also use `String`, `str::strip_prefix`,
  `str::is_empty`, `fmt::Formatter::debug_struct` and the formatting of
  `Rational`, `u64` and `i64`; they are not part of the canonical forms.

## Current deviations

None: the code and the tests follow every rule above.
