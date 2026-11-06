<picture>
  <source media="(prefers-color-scheme: dark)" srcset=".github/assets/logo-dark.svg">
  <img alt="kalyx" src=".github/assets/logo.svg" height="64">
</picture>

# kalyx

kalyx is the computer algebra library of casξ, a portable workstation for
mathematics, science and programming built on the Raspberry Pi 5. It computes
exact symbolic algebra, controlled-precision numerics and typed continuous
calculation for the casξ applications: kosmo, the casξ user interface, will
send it what you type and show what it computes. The name comes from the Greek
κάλυξ.

## Status

This repository is newly initialized. It holds this README, the kalyx logo,
the contribution rules, a `.gitignore`, a commit-message hook and the
repository checks, which continuous integration runs on every pull request to
`main` and on every push to `main`. There is no library code here, and the
library does not build or run from this repository yet.

The library is developed today in a separate repository that is not public.
Its code, tests, documentation and Lean proofs will move into this repository
together with their complete history. The move is planned for the close of the
library's current development stage, which covers the 0.5 releases; the
project owner may set a different time. Until the move, this repository
accepts no library code, and after it development continues here.

## What the library provides

The capabilities below are those of the library's current development tree;
they arrive here with the move. The library is an ordinary Rust `std` library with a command-line program and an
interactive session. It builds with stable Rust and supports only 64-bit
targets. The mathematical core runs on a host computer without the casξ
operating system, a GUI or an async executor, and it has no runtime dependency
on another computer algebra system, numerical library or floating-point
fallback.

- **Exact arithmetic and integers.** Rationals of arbitrary size; decimal
  literals are exact, so `0.1 + 0.2` is `3/10`. Integer GCD and extended GCD,
  modular powers and inverses, the Chinese remainder theorem, primality,
  integer factorization, factorials and binomial coefficients.
- **Polynomials and rational functions over Q.** Univariate and multivariate
  rings, division, GCD, resultants, discriminants, partial fractions,
  square-free decomposition, and factorization over Q and over embedded number
  fields. Rational functions keep the conditions of their source domain:
  cancelling `(x^2-1)/(x-1)` gives `x + 1` together with the exclusion
  `x - 1 != 0`.
- **Algebraic numbers.** Exact real and complex algebraic numbers, radicals,
  minimal polynomials and exact comparison.
- **Equations and sets.** Real polynomial and rational equations, exact real
  roots with isolating intervals and multiplicities, root counts on intervals,
  real sets and rational inequalities, Groebner bases and finite polynomial
  systems, parameter and elementary equations with guarded solution families,
  and ordinary differential equations with symbolic solutions (first-order
  linear, separable, and second-order with constant rational coefficients).
- **Symbolic calculus.** Function expressions with assumptions, guarded
  differentiation, indefinite and definite integration, limits, local series
  and sums.
- **Linear algebra.** Exact rational matrices, elimination and linear systems,
  reusable LU, matrices over algebraic numbers, parameters and functions,
  orthogonal and Hermitian decompositions, spectra and canonical forms, exact
  singular values, matrix functions, controlled-precision numerical matrices,
  and sparse matrices with iterative solvers.
- **Numerics.** Controlled-precision evaluation with rigorous enclosures,
  interval arithmetic, enclosures of elementary functions, certified bracketed
  roots and finite quadrature. Machine binary64 floating point is partially
  provided.
- **Nonlinear problems.** Real function models with structured derivatives,
  local roots, root-box certificates, weighted nonlinear least squares, local
  smooth optimization, explicit and implicit initial-value problems, and
  equilibrium and trajectory sensitivities.
- **Environments and programs.** Typed environments with versioned requests
  and atomic bindings, lexical user functions and programs with closures, and
  collection values (partially provided).

Every capability has one feature document, listed in a feature index with its
status, source modules and the Lean theorems registered for it. The feature
documents arrive with the code.

## Examples

These are results of the library's command-line program. The program and an
interactive session arrive here with the code; neither runs from this
repository yet.

| Input | Result |
| --- | --- |
| `0.1 + 0.2` | `3/10` |
| factor `x^4-1` | `(x - 1)*(x + 1)*(x^2 + 1)` |
| cancel `(x^2-1)/(x-1)` | `x + 1`, valid where `(x - 1) != 0` |
| real roots of `(x^2-2)^2*(x-1)` | `root(x^2 - 2, (-4, 0))` and `root(x^2 - 2, (5/4, 3/2))`, each of multiplicity 2, and `1` of multiplicity 1 |
| Groebner basis of `x*y-1`, `y^2-x` in `Q[x,y]`, lex order | `[x - y^2; y^3 - 1]`, a zero-dimensional ideal |
| definite integral of `1/(x^2+1)` over the real line | `pi` |
| the linear system `[[1, 2]] * x = [[3]]` | `x = [[3], [0]] + [[-2], [1]] * t` |

Requests are made with a fresh context per request, so that every stage draws
on the same work allowance, and a cloned cancellation token can cancel a
request from another thread. The interface is experimental: there is no stable
binary interface, serialization format, inter-process protocol or C ABI yet.

## How results behave

- Values stay exact unless a feature explicitly computes an enclosure or an
  approximation. Nothing is silently converted to floating point.
- Each mathematical domain is its own type, such as polynomials, rational
  functions, algebraic numbers, matrices over each coefficient domain, sets and
  enclosures. Conversions between them are explicit and checked.
- An `Err` means the request has no answer: invalid input, a domain error, an
  exhausted limit, cancellation or an expired deadline. An `Ok` result can
  carry a state such as not converged, insufficient precision, unevaluated, a
  condition set, a residual factor or an unknown box. An unevaluated result or
  a condition set does not assert that no solution exists. Completeness is
  promised only where a feature document states it.
- Every request runs under limits. `Limits::default()` allows, for example,
  65,536 bytes of input, 100,000 work units and polynomials of degree 256.
- The limit and cancellation checks are cooperative. A running big-integer
  primitive, allocation or formatting operation cannot be interrupted, an
  ordinary Rust allocation failure may abort the process, and the library has
  no memory quota, CPU-time guarantee or way to terminate a process. A host
  that needs these supplies them; on casξ that host is krepi.

The full rules are in the semantics document, which arrives with the code.

## Verification

Selected production functions are proved correct in Lean 4. Charon extracts
the Rust source of the library, Aeneas translates the extraction into Lean
definitions, and handwritten Lean proofs show that those definitions satisfy
specifications written independently of the code with Mathlib. A proof covers
exactly the functions and statements registered for it. Code outside a
registered target is unverified, the listed trusted inputs remain assumptions,
and the proofs say nothing about time, memory or the compiled binary.

The proof gate checks every registered target together with the tests. Its
pinned proof tools are installed by a setup command that currently needs macOS
on Apple silicon. The gate, the tools, the proof targets and the trusted
boundary are documented with the code.

## What kalyx aims to cover

The target scope of the library is divided into subject domains. Each domain
page describes the complete feature set of its domain, provided or planned,
and links the feature documents of what exists. The domain pages arrive with
the code.

| Domain | Scope |
| --- | --- |
| Functions | Elementary, discrete and distribution functions, the gamma family, error and exponential integrals, with symbolic forms, identities, derivatives, series and enclosed numerical values |
| Special functions | Bessel, elliptic, hypergeometric and zeta families, polylogarithms, Lambert W, orthogonal polynomials, formal functions and held operators |
| Simplification and assumption reasoning | Named canonical forms, trigonometric, logarithmic, radical and special-function simplification, zero testing with evidence, assumption reasoning, user rules, step-by-step derivations |
| Symbolic calculus | Indefinite integration by decision procedures, definite and multiple integrals with conditions, limits, generalized series, sums and products, integral transforms, singularity analysis |
| Equations, inequalities and recurrences | Transcendental equations, positive-dimensional polynomial systems, multivariate inequalities and quantifier elimination, Diophantine and recurrence equations, inverse functions |
| Symbolic differential equations | Classification, first-order and higher-order methods, linear systems, transform methods, boundary-value and eigenvalue problems, restricted partial differential equations |
| Algebraic structures and number theory | Finite fields, polynomials over general coefficient domains, ideals and varieties, matrices and lattices over integral domains, number-theoretic functions, factorization and primality certificates, combinatorics, permutation groups, Boolean algebra |
| Linear algebra | Spectra of parameter and symbolic matrices, generalized eigenproblems, further decompositions and matrix equations, polynomial matrices, large sparse problems, structured matrices, vector spaces and linear maps, verified numerical results |
| Vector calculus and tensors | Curvilinear coordinates, differential operators, field integrals, multidimensional arrays, indexed tensor algebra, differential geometry, differential forms |
| Numerical approximation, quadrature and transforms | Interpolation and approximation, quadrature, numerical and automatic differentiation, global scalar root finding, sequence acceleration, discrete transforms, the machine floating-point path |
| Optimization | Constrained nonlinear programming, derivative-free and large-scale methods, linear and quadratic programming, small integer programs, certified global optimization, symbolic extrema, fitting |
| Numerical differential equations | Explicit and implicit method families, events and discontinuities, differential-algebraic equations, boundary-value problems, verified integration, sensitivities and continuation, dynamical-systems analysis |
| Dimensions, units and constants | Dimension system, unit library and conversion, affine and logarithmic units, constants with their sources, uncertainty propagation, unit-aware operations |
| Data, probability and statistics | Data values, descriptive statistics, distributions, symbolic probability, reproducible random numbers, estimation and intervals, hypothesis tests, regression |
| Finance and dates | Time value of money, cash-flow measures, amortization and depreciation, interest-rate conversion, bonds, dates and day counts |
| Language, collections and workflow | Collection values, controlled iteration, function abstraction, modules and libraries, reactive dependencies, persistent sessions, jobs, the settings context |
| Serialization and interchange | Structured input and output, stable value encoding, an inter-process protocol, language bindings, compiled evaluation and code generation, checkable certificates, external data |
| Graphics and geometry | Reliable sampling, curves and regions, graph analysis, three-dimensional sampling, plot data for differential equations and statistics, an exact geometry kernel |

Shared components that several domains build on, such as the context budget,
coefficient fields, the function registry, numerical evaluators, rewriting,
collections, binary64, stable encoding and fast arithmetic, are described on
the cross-cutting page with their requirements, contracts, specifications and
proof paths.

Across all domains, a result that is not exact states its guarantee level:
exact, certified, estimated or heuristic. A solution set or search states
whether it is complete, partial with a residual, or unsolved. A decision states
its evidence: proved, refuted, numerical evidence or unknown. Settings such as
the angle unit, number base and exact or approximate mode are inputs of the
request and are echoed in the result, and every random operation takes an
explicit seed or stream.

The domains cover only what the mathematical core computes. Editing,
typesetting, rendering, interaction, documents and permissions belong to the
applications built on the library; for finance, graphics and geometry the
library provides the mathematical kernel only. Outside the target scope are
symbolic solution of general partial differential equations and complete
symbolic solution of general nonlinear systems, Markov chain Monte Carlo and
machine-learning models, finitely presented groups, representation theory and
homological algebra, a library of graph algorithms and optimal control,
noncommutative and operator algebras and dedicated physics modules, automated
theorem proving beyond the restricted geometric and inequality proofs of the
domains, and natural-language input.

## kalyx in casξ

- **krepi** ([casxi-lab/krepi](https://github.com/casxi-lab/krepi)) is the
  casξ operating system, a microkernel for the Raspberry Pi 5. kalyx will run
  on it as an ordinary user program, outside the kernel. krepi is planned to
  supply what the library leaves to its host: running a calculation as a job
  with its own resource budget, cancellation, a forced stop and reclamation of
  its resources. Its first release is planned to run the casξ calculator,
  built from a pinned commit of this library, as such a job over the serial
  console, with the same output bytes on a development host, on QEMU and on
  the Raspberry Pi 5. krepi is newly initialized, and none of this works yet.
- **kosmo** ([casxi-lab/kosmo](https://github.com/casxi-lab/kosmo)) is the
  casξ user interface and shell. It will turn what you type into expressions
  for kalyx and show the results it computes, with formula editing,
  typesetting, graphs and documents. kalyx has no GUI and does not depend on
  kosmo. kosmo is newly initialized as well.

| Repository | Role |
| --- | --- |
| [casxi-lab/krepi](https://github.com/casxi-lab/krepi) | The casξ operating system |
| [casxi-lab/kosmo](https://github.com/casxi-lab/kosmo) | The casξ user interface and shell |

## Documentation

The library documentation (semantics, feature index, subject domains, command
line and interactive session, formal verification, architecture and
validation) moves here with the code. Rules for this repository:
[AGENTS](AGENTS.md) and [CONTRIBUTING](CONTRIBUTING.md).

## License

kalyx is released under the [MIT License](LICENSE). Copyright (c) 2026 The
casξ Authors; see [AUTHORS](AUTHORS).
