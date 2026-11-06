<picture>
  <source media="(prefers-color-scheme: dark)" srcset=".github/assets/logo-dark.svg">
  <img alt="kalyx" src=".github/assets/logo.svg" height="64">
</picture>

# kalyx

kalyx is the computer algebra library of casξ, a portable workstation for
mathematics, science and programming built on the Raspberry Pi 5. It is being
built to compute exact symbolic algebra, controlled-precision numerics and
typed continuous calculation for the casξ applications: kosmo, the casξ user
interface, will send it what you type and show what it computes. The name
comes from the Greek κάλυξ.

## Status

kalyx is being built from its foundations, and it has no usable capabilities
yet. The repository holds a Rust package named `kalyx` with an empty library
and a command-line program that has no commands, the repository checks that
continuous integration runs on every pull request to `main` and on every push
to `main`, and the [porting record](PORTING.md), still empty, of code taken
over from an earlier implementation of the casξ computer algebra system. That
earlier implementation is not public; it serves as a reference, and its
answers are to be used as test vectors for kalyx.

The first release, 0.1, is planned to provide the base of the library and a
small slice of algebra on it: an exact rational number type, a parser, an
expression core with canonical forms, univariate polynomials over
$\mathbb{Q}$ with expansion and differentiation, structured errors and result
states, and a command entry that runs each request under a work budget, a
deadline and cancellation, with a minimal command-line program. Later
releases complete the shared foundations (coefficient fields, the function
registry, numerical evaluators with rigorous enclosures, collection values,
stable value encoding and a machine floating-point path) and then build the
subject domains below on them. None of this is available yet.

## Build

Building needs the Rust toolchain that `rust-toolchain.toml` pins and a 64-bit
target; the crate does not compile for other pointer widths.

```sh
rustup toolchain install
cargo build --locked
cargo test --locked
```

The library has no public items yet, and the program exits without output
(`cargo run --quiet` prints nothing).

## Rules the library is built to

- Values stay exact unless an operation explicitly computes an enclosure or an
  approximation; the library code forbids `unsafe` code and denies
  floating-point arithmetic until the machine floating-point path is added.
- Every request will run under explicit limits, a deadline and cancellation,
  checked cooperatively; the library uses no threads, hash containers,
  wall-clock time, thread-local state or unwinding recovery, and no
  transcendental functions of the platform math library.
- The library has no third-party dependencies; adding one is a reviewed
  change of its own.
- Code taken over from the earlier implementation is recorded in
  [PORTING.md](PORTING.md) and tested again here; its tests, proofs and
  results are not evidence for kalyx.

## What kalyx aims to cover

The target scope of the library is divided into subject domains. A domain
page describing the complete feature set of a domain is added when work on that
domain starts.

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
collections, the machine floating-point path, stable encoding and fast
arithmetic, are built first;
each gets its requirements, contract, specification and proof path when it is
added.

Across all domains, a result that is not exact is to state its guarantee
level: exact, certified, estimated or heuristic. A solution set or search is to
state whether it is complete, partial with a residual, or unsolved, and a
decision its evidence: proved, refuted, numerical evidence or unknown. Settings
such as the angle unit, number base and exact or approximate mode are to be
inputs of the request, echoed in the result, and every random operation is to
take an explicit seed or stream.

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
  the Raspberry Pi 5. krepi is at an early stage, and none of this works yet.
- **kosmo** ([casxi-lab/kosmo](https://github.com/casxi-lab/kosmo)) is the
  casξ user interface and shell. It will turn what you type into expressions
  for kalyx and show the results it computes, with formula editing,
  typesetting, graphs and documents. kalyx has no GUI and does not depend on
  kosmo. kosmo is at an early stage as well.

| Repository | Role |
| --- | --- |
| [casxi-lab/krepi](https://github.com/casxi-lab/krepi) | The casξ operating system |
| [casxi-lab/kosmo](https://github.com/casxi-lab/kosmo) | The casξ user interface and shell |

## Documentation

The library documentation (semantics, feature documents, subject domains,
architecture and validation) is added as each part is built. Rules for this
repository: [AGENTS](AGENTS.md) and [CONTRIBUTING](CONTRIBUTING.md); code taken
over from the earlier implementation: [PORTING](PORTING.md).

## License

kalyx is released under the [MIT License](LICENSE). Copyright (c) 2026 The
casξ Authors; see [AUTHORS](AUTHORS).
