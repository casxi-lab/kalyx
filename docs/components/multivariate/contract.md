# Multivariate polynomials

This contract states the multivariate polynomials of kalyx and their
monomial orders: the ring $K[x_1, \ldots, x_n]$ of finitely many variables
over a coefficient ring $K$ with a monomial order, and its polynomials; the
monomial orders `lex`, `grlex`, `grevlex` and the block elimination orders;
the canonical form of a polynomial, its leading term, its total degree and
whether it is monic; the normalization of a list of terms; the ring
operations and powers; and over $\mathbb{Q}$ the expansion of a term into a
polynomial and the conversion of a polynomial back into a term. In this
release it holds the numbered requirements of the component and the
statements of its Lean specification; the interface, the rules of the
implementation, the storage cost, the charges and the testing obligations are
added with the implementation. The
[architecture](../../architecture.md#later-foundations) places the component
among the later foundations and states the design rules of the
[coefficient-field trait](../../architecture.md#coefficient-field-trait) that
the polynomials are built on. The coefficient-field trait, $\mathbb{Q}$ and
the prime fields belong to the [exact numbers](../numbers/contract.md), the
terms to the [term core](../terms/contract.md), the errors to the
[errors and result states](../errors/contract.md), and the polynomials of one
variable to the [polynomials](../polynomials/contract.md).

**Status.** Not implemented; the multivariate polynomials and the monomial
orders are planned for release 0.2, at tier A2 (specification checked), as
the [architecture](../../architecture.md#later-foundations) lists. Their Lean
specification is in `verification/Kalyx/Spec/Multivariate/`, and
`verification/statements.json` records the state of its statements, as
[requirements and statements](#requirements-and-statements) lists. The
specification is written anew for kalyx; the strict orders of `grevlex` and
of the block orders are taken over from the specification of the earlier
implementation as definitions only, as [PORTING](../../../PORTING.md)
records. The first caller of the component in the library is planned to be
the basic polynomial algorithms over $\mathbb{Q}$, in release 0.2.

## Scope

- **Included.** The multivariate rings over a coefficient ring, with the
  monomial orders `lex`, `grlex`, `grevlex` and the block elimination orders
  whose two blocks are both ordered by `grevlex`; the canonical form of a
  polynomial, its leading term, its total degree and whether it is monic;
  the normalization of a list of terms; zero, one, the variables, constants,
  negation, sums, differences, products and powers, generic over the
  coefficient ring; and over $\mathbb{Q}$ the expansion of a term into a
  polynomial and the conversion of a polynomial back into a term. They are
  stated as numbered requirements, planned for release 0.2, with their
  executable specification (tier A2) in Lean, its statements and the replays
  of its vectors.
- **Excluded, with their owners.**
  - The implementation of the component, with its interface, the rules of
    its operations, the storage cost of a polynomial, the checks of the
    limits, the charges of every step and the testing obligations; the
    comparison of two rings with `same_parent` and its charge, the pair check
    that fails with `VariableMismatch` for polynomials of different rings,
    and a multivariate ring as a coefficient ring with its storage cost; and
    partial derivatives, evaluation and substitution: the implementation of
    the multivariate polynomials, release 0.2, which adds them to this
    contract.
  - The refinement of the monomial orders by the comparison of the
    implementation, with the order tag and the cached total degree of a
    monomial and the helpers of the comparison (tier A3): the A3 upgrade of
    the monomial orders that the
    [architecture](../../architecture.md#later-foundations) plans.
  - Reading the roles `variables` and `monomial_order` of a request into a
    ring, the names of the orders, the display text of rings and
    polynomials, the monic form, the multivariate GCD and factorization: the
    multivariate operations of the command entry over $\mathbb{Q}$, release
    0.2. Coefficients other than $\mathbb{Q}$ in a request, and the
    expansion of terms over them: release 0.4.
  - Block orders with other orders in their blocks, the elimination of
    variables with a Gröbner basis and the restriction of an order to the
    remaining variables, ordered multivariate division and Gröbner bases:
    release 0.4. Multivariate rational functions: release 0.4.
  - An exponent vector whose length is not the number of variables and a
    block split above the number of variables, which the earlier
    implementation rejected with `DimensionMismatch`: the specification
    excludes both by their types, and the fault kind `DimensionMismatch` is
    appended in release 0.3, as the
    [errors and result states](../errors/contract.md#kinds-of-the-earlier-implementation)
    list.
  - The faults of an exponent that is not a constant or not an integer: the
    exponents of the [term core](../terms/contract.md) are integers, so the
    expansion meets neither. The canonical form of a single coefficient: the
    coefficient ring, such as the rationals of the
    [exact numbers](../numbers/contract.md#fld-r01).

## Requirements

The identifiers `FLD-R` are those of the coefficient fields of the earlier
implementation of the casξ computer algebra system, and each such entry
states the part of the requirement that applies to the multivariate
polynomials. The other requirements of the component have no identifier
there: the component numbers them `MVP-R01` to `MVP-R07`, each with a name of
what it states. No identifier is ever renumbered or reused. Every
requirement is planned for release 0.2 and not implemented yet. The Lean
specification states every requirement, as
[requirements and statements](#requirements-and-statements) lists; the tests
come with the implementation.

### FLD-R06

**Monomial orders.** Planned for release 0.2: a monomial in $n$ variables is
its exponent vector, $n$ natural numbers, the first variable the most
significant, and the product of two monomials is the sum of their vectors.
`lex` compares the exponents from the first variable; `grlex` compares the
total degree first and then as `lex`; `grevlex` compares the total degree
first and then lets the smaller exponent at the last variable where the
exponents differ belong to the greater monomial. The block order of the
split $k$, with $0 \le k \le n$, compares the first $k$ variables by
`grevlex` and, when they are equal, the last $n - k$ variables by `grevlex`;
for $k = 0$ and $k = n$ it compares monomials as `grevlex` does.
Elimination property: under the block order of the split $k$, a monomial
that contains one of the first $k$ variables is greater than every monomial
in the last $n - k$ variables alone. Each order is a strict total order,
compatible with multiplication and well founded, the constant monomial is
the least, and each is the order of a monomial order of Mathlib on the
variables. The comparison of each order is computable. In
$\mathbb{Q}[x, y, z]$ the leading term of $x^2 + x z^2 + y^2 z$ is $x^2$
under `lex`, $x z^2$ under `grlex` and $y^2 z$ under `grevlex`; under the
block order of the split 1 the leading term of $x y + x z^2 + y^4$ is
$x z^2$.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### FLD-R01

**Canonical forms.** Planned for release 0.2, the part of the multivariate
polynomials: a polynomial is stored as the list of its terms, each the
exponent vector of a monomial with a coefficient of the coefficient ring.
The stored form is canonical when the vectors increase strictly under the
order of the ring, so that the last term is the leading term and no
monomial repeats, and every coefficient is a canonical element of the parent
of the coefficient ring that is not zero, which its zero test decides; so
the zero polynomial has no term. A polynomial means the polynomial of
Mathlib in its variables over the interpretation of the coefficient ring,
the sum of the monomials of its terms. Canonical forms are unique under this
interpretation, and when every element of the coefficient ring has a
canonical form, so does every polynomial. The length of an exponent vector
is the number of variables of the ring.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R01

**The ring.** Planned for release 0.2: a ring holds the parent of its
coefficient ring, the names of its variables in their order, the first
variable the most significant, and its monomial order. The list of names may
be empty, which is the ring without variables, whose only monomial is the
constant one, and the split of a block order is at most the number of
variables. Building a ring checks the names one after the other, in their
order: each name first follows the rule of
[symbol names](../terms/contract.md#symbol-names), and a malformed or
reserved name fails as the symbol constructor of the term core fails, with
`Syntax` or `Unsupported` and its span; then a name equal to an earlier one
fails with `Syntax`, without a span. The first failure is the result, so in
the names `x`, `x`, `pi` the repeated `x` fails before the reserved `pi`.
Names are compared byte by byte, so they are case-sensitive. Two rings are
the same exactly when their parents of the coefficient ring, their names in
their order and their orders, a block order with its split, are equal: the
rings of the variables $x, y$ and $y, x$ differ, and so do the rings of
`grevlex` and of the block orders of the splits $0$ and $n$, which compare
monomials alike. The operations of a ring take it as their receiver and
assume that their operands belong to it; they never compare rings.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R02

**Leading terms, degree and monic polynomials.** Planned for release 0.2:
the leading term of a nonzero polynomial is the term of its greatest
monomial under the order of the ring, the last term of its canonical form.
Under every monomial order of Mathlib that agrees with the order of the
ring, its exponent vector and its coefficient are the degree and the leading
coefficient of the polynomial of Mathlib that the polynomial means. The
total degree is the largest total degree of the monomials of its terms, that
of the polynomial of Mathlib. The zero polynomial has no leading term and no
total degree. A polynomial is monic when its leading coefficient is 1, which
the zero test of the difference of the leading coefficient and 1 decides; so
whether it is monic depends on the order: $x - 2y^2$ is monic under `lex`,
with the leading term $x$, and not under `grlex`, with the leading term
$-2y^2$. The zero polynomial is not monic, also over the zero ring, where
the zero polynomial of Mathlib is monic.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R03

**Normalization of term lists.** Planned for release 0.2: the polynomial of
a list of terms, each a pair of an exponent vector and a coefficient, not a
term of the term core, in any order and possibly with repeated monomials.
The terms are sorted by the order of the ring, the coefficients of each
monomial are added by the coefficient ring, and then every term whose
coefficient the zero test finds zero is dropped. When every coefficient of
the list is a canonical element of the parent of the coefficient ring, the
result is the canonical form of the sum of the terms, and every permutation
of the list gives the same polynomial: under `lex`, $x z^2$, $x^2$, $y^2 z$,
$x^2$ give $y^2 z$, $x z^2$, $2x^2$, and $x y$, $-x y$ give the zero
polynomial, with no term. Normalization does not bring a coefficient to its
canonical form, so a coefficient that is not canonical and occurs once is
kept as it is.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R04

**One implementation for every coefficient ring.** Planned for release 0.2:
the stored form, the canonical forms, normalization, the leading term and
the ring operations of [MVP-R05](#mvp-r05) and [FLD-R03](#fld-r03) exist
once, for every coefficient ring of the coefficient-field trait whose zero
test always decides, $\mathbb{Q}$ and the prime fields among them. They take
the coefficient ring as a parameter, reach the coefficients only through its
methods, obtain an integer only as $n \cdot 1$ and divide no coefficient, so
they hold in every characteristic, and a polynomial means its
interpretation through that of the coefficient ring. The same normalization
gives $5xy$ for $3xy$ and $2xy$ over $\mathbb{Q}$, and the zero polynomial
over $\mathbb F_5$. The expansion of terms and the conversion back to terms,
[MVP-R06](#mvp-r06) and [MVP-R07](#mvp-r07), are over $\mathbb{Q}$ only.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R05

**Ring operations.** Planned for release 0.2: zero, one, the variable at a
position below the number of variables, the constant of an element of the
coefficient ring, negation, sums, differences and products of a ring. A
constant that the zero test finds zero is the zero polynomial. A sum or a
difference merges the terms of its operands by increasing monomials under
the order of the ring, adds or subtracts the coefficients of a monomial that
both operands have and drops the term when the zero test finds the result
zero; a product multiplies every term of its left operand by every term of
its right one and normalizes the products as [MVP-R03](#mvp-r03) does. On
canonical operands, whose coefficients are canonical elements of the parent
of the coefficient ring, the result is canonical and means the same
operation of Mathlib on the polynomials that the operands mean: in
$\mathbb{Q}[x, y]$ under `lex`, $(x + y)(x - y)$ is $x^2 - y^2$, stored as
$-y^2$, $x^2$, and $x - x$ is the zero polynomial, with no term, not a term
with the coefficient 0. The operations read no limits and add no failure of
their own: their only failures are those of the methods of the coefficient
ring that they call, passed on unchanged, and over a coefficient ring with
its ring laws and an exact zero test none arises on canonical operands.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### FLD-R03

**Integer powers.** Planned for release 0.2, the part of the multivariate
polynomials: the power of a polynomial to a natural exponent $k$, by
repeated squaring from the highest binary digit of $k$, with $a^0 = 1$ for
every polynomial $a$, including $0^0 = 1$, and $0^k = 0$ for $k \ge 1$. On
a canonical operand, as in [MVP-R05](#mvp-r05), the result is canonical and
means the power of Mathlib, so over $\mathbb F_2$ the square of $x + y$ is
$x^2 + y^2$. A ring of polynomials has no inverses, so there are no negative
powers; a negative power in a term fails its expansion, as
[MVP-R06](#mvp-r06) states. The limits of the exponent and of the degree,
the order of their checks and the charges of the squarings are not part of
this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R06

**Expansion of terms.** Planned for release 0.2: a canonical term of the
[term core](../terms/contract.md) is expanded into a polynomial of a ring
over $\mathbb{Q}$. The nodes are walked from the root, each node before its
children and the children in their stored order, and the first failure is
the result: a number is the constant of its value; a symbol whose name is
the name of a variable of the ring is that variable, and any other symbol
fails with `UnknownSymbol`; sums, products and powers with a nonnegative
exponent are the sums, the products and the powers of the polynomials of
their parts, by the operations of [MVP-R05](#mvp-r05) and
[FLD-R03](#fld-r03). A power expands its base first, so $z^{-1}$ in
$\mathbb{Q}[x, y]$ fails with `UnknownSymbol`, and then fails with
`NotPolynomial` when its exponent is negative, so $x / y$ fails with
`NotPolynomial`. A constant, a call and a condition of the term core fail
with `NotPolynomial`, a call before its arguments, as in the expansion of
the [polynomials](../polynomials/contract.md#expansion). Coefficients that
cancel leave no term. When a term expands into a polynomial, the term is
defined at every assignment, and its value is the value of the polynomial
at the values of the names of the variables.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### MVP-R07

**Conversion back to terms.** Planned for release 0.2: a polynomial of a
ring over $\mathbb{Q}$ is converted back into a term of the term core only
through the constructors of the term core, those of symbols, powers,
products and sums. Each term of the polynomial, in its stored order, becomes
the product of the number of its coefficient and the powers of the variables
whose exponents are positive, in the order of the variables, a variable
with the exponent 1 being its symbol, or the number of its coefficient alone
for the constant monomial; their sum is the term of the polynomial, so the
zero polynomial is the number 0, a polynomial of one term is the term of
that term, and $3xy$ is a product, not a sum. The order of terms of the term
core and the limit `max_exponent` that the constructors read are parameters
of the conversion, and it reads no other limit. Its failures are those of
the constructors: when the names of the variables pass the check of
[MVP-R01](#mvp-r01), the conversion of a canonical polynomial returns a term
or fails with `ResourceLimit` naming `max_exponent`. The term that it
returns is canonical and has the value of the polynomial at every
assignment, and when the names of the variables are distinct, as in every
ring that [MVP-R01](#mvp-r01) builds, it expands back into the polynomial by
[MVP-R06](#mvp-r06). A ring with a repeated name, which [MVP-R01](#mvp-r01)
does not build, would expand a variable back as the first variable of its
name. The display text of a polynomial and
the charges of the conversion are not part of this entry.

- **Implemented here.** Nothing yet; planned for release 0.2.
- **Evidence.** The statements of the specification that
  [requirements and statements](#requirements-and-statements) lists; the
  tests come with the implementation.

### Requirements and statements

The Lean specification in
[`verification/Kalyx/Spec/Multivariate/`](../../../verification/Kalyx/Spec/Multivariate)
states the requirements above, written from them and from the design rules
of the architecture, not from code: the exponent vectors and the four
monomial orders, each as a strict order and as a computable comparison; the
ring; the stored form, the canonical forms and normalization; the ring
operations and powers; and over $\mathbb{Q}$ the expansion of terms and the
conversion back to terms. Its polynomials and operations are computable
definitions over the coefficient rings of the
[specification of the exact numbers](../numbers/contract.md#requirements-and-statements),
and its terms are those of the
[specification of the term core](../terms/contract.md#requirements-and-statements);
it imports both and restates neither, and it imports nothing of the
specification of the polynomials of one variable. Its operations read no
limits: each is a total function of its operands but for the outcomes of the
methods of the coefficient ring and of the constructors of the term core,
which it passes on, and a result is a value, a fault (of the coefficient
fields, of the term core, or `NotPolynomial`) or `ResourceLimit`, which only
such a method or constructor reports. The only limit that appears is the
`max_exponent` of the constructors of the term core, a parameter of the
conversion back to terms; the checks of the limits, the storage cost and the
charges are not stated. The meaning of a polynomial is its interpretation in
the polynomials `MvPolynomial (Fin n)` of Mathlib over the interpretation of
its coefficients. The specification builds no monomial order of Mathlib: one
statement says that each of its orders is the order of a monomial order of
Mathlib, and the statement about leading terms holds for every monomial
order of Mathlib that agrees with the order of the ring.

The properties of the polynomials hold for every coefficient ring of the
specification of the exact numbers whose ring laws hold and whose zero test
is exact under its interpretation, as for $\mathbb{Q}$ and $\mathbb F_p$.
The operations and normalization are stated on coefficients that are
canonical elements of the parent of the coefficient ring, and the existence
of canonical forms for coefficient rings whose every element has one. The
expansion keeps the meaning of a term under every interpretation of its
calls, conditions and constants, and the conversion back to terms under
every total order of the term core and every lawful interpretation, the
parameters of the statements about the term core, with the rules of calls
that keep every call; that the converted term expands back into the
polynomial is stated for rings whose names are distinct, and that the
conversion fails only with `ResourceLimit` naming `max_exponent` for rings
whose names pass the check of [MVP-R01](#mvp-r01).

The propositions of
[`verification/Kalyx/Statements/Multivariate.lean`](../../../verification/Kalyx/Statements/Multivariate.lean)
are its registered statements: ten properties, and a positive and a negative
example of each requirement, which fix the sample order of terms and the
default `max_exponent` of the term core where they convert back to terms; an
example in $\mathbb F_p$ names the field that `PrimeField.new p` builds.
`verification/statements.json` registers them with the theorems of the
modules in
[`verification/Kalyx/Proofs/Multivariate/`](../../../verification/Kalyx/Proofs/Multivariate)
and records the state of each.
[`verification/Kalyx/SpecTests/Multivariate.lean`](../../../verification/Kalyx/SpecTests/Multivariate.lean)
replays through the specification, with `#guard`, the four examples of the
monomial orders in the requirements of the coefficient fields of the earlier
implementation that [FLD-R06](#fld-r06) states, `ex1-lex`, `ex1-grlex`,
`ex1-grevlex` and `ex7-block1`, and the three vectors of
[`vectors/cli_cases.tsv`](../../../vectors/cli_cases.tsv) whose answers the
specification decides: `algebra/mpoly-expands-square`, the expansion of
$(x + y)^2$ and its conversion back to a term,
`algebra/poly-ring-rejects-repeated-variable` and
`algebra/poly-ring-with-grevlex-order`. Reading the arguments of a vector
into a ring and a term, and the display of rings and polynomials, belong to
the command surface.

| Requirement | Properties | Positive example | Negative example |
| --- | --- | --- | --- |
| [FLD-R06](#fld-r06) | `MonomialOrdersAreStrictTotalOrders`, `MonomialOrdersRespectProducts`, `MonomialOrdersAreWellFounded`, `TheConstantMonomialIsLeast`, `BlockOrdersEliminateTheirFirstBlock`, `MonomialOrdersAreThoseOfMathlib` | `ComparisonsUnderGrevlexAndABlockOrder` | `ComparisonsOfOtherOrdersDoNotHold` |
| [FLD-R01](#fld-r01) | `RingOperationsAreExact` | `CanonicalFormOfThreeTerms` | `NonCanonicalTermLists` |
| [MVP-R01](#mvp-r01) | None | `RingsAreBuiltFromTheirData` | `RepeatedNamesAndDifferentRings` |
| [MVP-R02](#mvp-r02) | `LeadingTermsAreThoseOfMathlib` | `LeadingMonomialsDependOnTheOrder` | `MonicDependsOnTheOrder` |
| [MVP-R03](#mvp-r03) | `NormalizationGivesCanonicalForms` | `NormalizationSortsAndAddsTerms` | `CancellingTermsLeaveNoTerm` |
| [MVP-R04](#mvp-r04) | `RingOperationsAreExact`, `NormalizationGivesCanonicalForms` | `OneNormalizationForEveryCoefficientRing` | `TermsVanishingModuloTwoLeaveNoTerm` |
| [MVP-R05](#mvp-r05) | `RingOperationsAreExact` | `SumsAndProductsOfBinomials` | `ZeroCoefficientsLeaveNoTerm` |
| [FLD-R03](#fld-r03) | `RingOperationsAreExact` | `PowersOfABinomialAndOfZero` | `PowersModuloTwoAndPowersOfZero` |
| [MVP-R06](#mvp-r06) | `ExpansionAndConversionKeepMeanings` | `TermsExpandIntoPolynomials` | `ForeignSymbolsAndNegativePowersFail` |
| [MVP-R07](#mvp-r07) | `ExpansionAndConversionKeepMeanings` | `PolynomialsConvertBackToTerms` | `ConversionBuildsCanonicalTerms` |
