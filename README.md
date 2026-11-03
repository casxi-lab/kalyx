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
the contribution rules, a `.gitignore` and a commit-message hook. There is no
code here, and nothing in this repository builds or runs yet.

The library exists today as
[erthoaers/casxi-cas](https://github.com/erthoaers/casxi-cas), version 0.4.0.
The capabilities and commands on this page are those of casxi-cas, and the
commands run from a checkout of casxi-cas today.

## Moving into kalyx

- The code, tests, documentation and Lean proofs of casxi-cas will move into
  this repository together with the complete Git history of casxi-cas.
- The move is planned for the close of the current casxi-cas development
  stage, which covers the 0.5 releases. The project owner may set a different
  time.
- Until the move, the library is developed in casxi-cas. Send changes there,
  following its `AGENTS.md` and `CONTRIBUTING.md`. This repository accepts no
  code before the move.
- After the move, development continues here and casxi-cas is frozen.
- The names in the examples below, the `casxi-cas` package and command and the
  `casxi_cas` crate, are the names casxi-cas uses today.

## What the library does today

casxi-cas is an ordinary Rust `std` library with a command-line program and an
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

Every capability has one feature document. The
[feature index](https://github.com/erthoaers/casxi-cas/blob/main/docs/features/README.md)
lists them with their status, source modules and the Lean theorems registered
for each.

## Try it

Run these from a checkout of casxi-cas. Dependencies are locked in
`Cargo.lock`.

```sh
cargo run --locked -- eval '0.1 + 0.2'
# 3/10
cargo run --locked -- factor 'x^4-1'
# (x - 1)*(x + 1)*(x^2 + 1)
cargo run --locked -- cancel '(x^2-1)/(x-1)'
# x + 1; domain: (x - 1) != 0
cargo run --locked -- roots '(x^2-2)^2*(x-1)'
# root(x^2 - 2, (-4, 0)); multiplicity: 2
# 1; multiplicity: 1
# root(x^2 - 2, (5/4, 3/2)); multiplicity: 2
cargo run --locked -- groebner 'Q[x,y]:lex' 'x*y-1' 'y^2-x'
# Q[x,y]; order: lex
# ideal: zero-dimensional
# basis: [x - y^2; y^3 - 1]
cargo run --locked -- f-defint '{}' '1/(x^2+1)' x -inf inf
# definite_integral(((1 + (x)^(2)))^(-1) assuming {x:real}, x, -inf, +inf): Converged; value: pi
cargo run --locked -- linsolve '[[1, 2]]' '[[3]]'
# affine: x = [[3], [0]] + [[-2], [1]] * t; free columns = [1]
cargo run --locked -- repl
```

`--help` lists the commands. Quote expressions that contain spaces or shell
operators. Results go to stdout and diagnostics to stderr. The exit status is 0
for success, 1 for computation and input errors, and 2 for command-line usage
errors.

The `repl` command keeps an isolated in-memory environment across input lines. Type one
calculation per line; `let a = 1/3` binds a name, `:get a` and `:clear a` read
and remove a binding, `:help` lists the session commands and `:quit` ends the
session. An erroneous line is reported and the session continues. Nothing is
saved to disk automatically.

## Use it from Rust

```rust
use casxi_cas::{Context, Polynomial, parse};

let mut context = Context::default();
let expression = parse("(x + 1)^3", &mut context)?;
let polynomial = Polynomial::from_expression(&expression, "x", &mut context)?;
let derivative = polynomial.derivative(&mut context)?;
assert_eq!(derivative.to_string(), "3*x^2 + 6*x + 3");
# Ok::<(), casxi_cas::Error>(())
```

Use a fresh `Context` for each request and pass it through parsing and
computation, so that every stage draws on the same work allowance. A cloned
`CancellationToken` can cancel the request from another thread. The interface
is experimental: there is no stable binary interface, serialization format,
inter-process protocol or C ABI yet.

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

The full rules are in
[semantics](https://github.com/erthoaers/casxi-cas/blob/main/docs/semantics.md).

## Verification

Selected production functions are proved correct in Lean 4. Charon extracts
the Rust source of the library, Aeneas translates the extraction into Lean
definitions, and handwritten Lean proofs show that those definitions satisfy
specifications written independently of the code with Mathlib. A proof covers
exactly the functions and statements registered for it. Code outside a
registered target is unverified, the listed trusted inputs remain assumptions,
and the proofs say nothing about time, memory or the compiled binary.

In casxi-cas:

```sh
cargo xtask check --skip-formal   # formatting, Clippy, tests, doc tests, benchmark build, documentation check
cargo xtask check                 # the same, together with the proof gate
cargo xtask formal run            # the proof gate alone
```

The proof gate needs the pinned proof tools. `cargo xtask formal setup`
installs them and needs macOS on Apple silicon. See
[formal verification](https://github.com/erthoaers/casxi-cas/blob/main/docs/formal-verification.md)
for the tools, the proof targets and the trusted boundary.

## What kalyx aims to cover

The target scope of the library is divided into subject domains. Each domain
page describes the complete feature set of its domain, provided or planned,
and links the feature documents of what exists. The domain pages are in
[subject domains](https://github.com/erthoaers/casxi-cas/blob/main/docs/domains/README.md).

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
the [cross-cutting](https://github.com/erthoaers/casxi-cas/blob/main/docs/domains/cross-cutting/README.md)
page with their requirements, contracts, specifications and proof paths.

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
| [erthoaers/casxi-cas](https://github.com/erthoaers/casxi-cas) | The library today: code, tests, documentation, proofs and history, until they move here |
| [casxi-lab/krepi](https://github.com/casxi-lab/krepi) | The casξ operating system |
| [casxi-lab/kosmo](https://github.com/casxi-lab/kosmo) | The casξ user interface and shell |
| [erthoaers/casxi-build](https://github.com/erthoaers/casxi-build) | Project planning, decisions and progress, written in Chinese |

## Documentation

All library documentation is in casxi-cas until the move:

| Document | Contents |
| --- | --- |
| [README](https://github.com/erthoaers/casxi-cas/blob/main/README.md) | Running, validating and measuring the library |
| [Semantics](https://github.com/erthoaers/casxi-cas/blob/main/docs/semantics.md) | Input syntax, exact values, results, states, errors and limits |
| [Feature index](https://github.com/erthoaers/casxi-cas/blob/main/docs/features/README.md) | Every capability provided today, with its status |
| [Subject domains](https://github.com/erthoaers/casxi-cas/blob/main/docs/domains/README.md) | The complete target scope, one page per domain |
| [Command line](https://github.com/erthoaers/casxi-cas/blob/main/docs/features/interface/cli.md) and [REPL](https://github.com/erthoaers/casxi-cas/blob/main/docs/features/interface/repl.md) | Command syntax and the interactive session |
| [Formal verification](https://github.com/erthoaers/casxi-cas/blob/main/docs/formal-verification.md) | Proof tools, targets and the trusted boundary |
| [Architecture](https://github.com/erthoaers/casxi-cas/blob/main/docs/architecture.md) | Design and source layout |
| [Validation](https://github.com/erthoaers/casxi-cas/blob/main/docs/validation.md) | Tests, benchmarks and measurement programs |

Rules for this repository: [AGENTS](AGENTS.md) and
[CONTRIBUTING](CONTRIBUTING.md).

## License

A license has not been selected yet. casxi-cas is not enabled for publication.
