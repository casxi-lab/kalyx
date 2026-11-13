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

## What kalyx can do now

kalyx is being built from its foundations. This version computes exactly
over the rational numbers and over univariate polynomials with rational
coefficients, through three operations:

- `eval` evaluates an expression of numbers to its exact rational value:
  `+`, `-`, `*`, `/`, `^` with integer exponents, parentheses and unary
  minus; decimal literals such as `0.1` are exact;
- `expand` expands an expression as a polynomial in one variable over
  $\mathbb{Q}$; any other symbol is an error;
- `diff` returns the derivative of that polynomial by the variable.

The library also holds the integer kernel of `kalyx::number`: checked
arithmetic of integers, GCDs with Bézout coefficients, modular inverses and
powers, and Chinese remaindering, which no operation reaches yet.

Every request runs under explicit limits on its work, its input and output
bytes, its nesting depth, the size of its values, the bits of its integers
and its exponents; a caller of the library can also give it a deadline and
cancel it. A request that exceeds a limit fails with a `ResourceLimit`
error that names the limit. Results come out as one line of tab-separated
fields per request, the only output format, which the
[output lines](docs/semantics.md#output-lines) state byte for byte.

The repository holds the Rust package `kalyx`, with the library and the
command-line program `kalyx`; the repository checks, which continuous
integration runs on every pull request to `main` and on every push to
`main`; the [porting record](PORTING.md) of code taken over from an earlier
implementation of the casξ computer algebra system and of the proof tooling
taken over from krepi, the kernel of casξ; and 58
[answer vectors](vectors/README.md), converted from that earlier
implementation's fixtures, which are all replayed through the library and
through the program. The earlier implementation is not public; it serves as
a reference and as a source of test vectors. The proof tooling in
`verification/` and `xtask/src/formal/` provides the commands of
`cargo xtask formal` and two steps of the checks, and CI runs its proof gate;
nothing about kalyx is proved yet.

## Build and run

Building needs the Rust toolchain that `rust-toolchain.toml` pins and a 64-bit
target; the crate does not compile for other pointer widths.

```sh
rustup toolchain install
cargo build --locked
cargo test --locked
cargo run --quiet -- eval '1/3 + 1/6'
```

The program is built as `target/debug/kalyx`; `cargo build --locked
--release` builds `target/release/kalyx`. `kalyx --version` prints the name
and the version of the package, and `kalyx --help` the usage.

## The command-line program

The program writes the result of each request as one line on standard
output. In the examples below, `⇥` stands for a tab. The fields of a line are its kind, `value` or `error`,
the input, context and settings versions of the request, which the program
always sets to 0, and then the result: the value, or the kind, span, limit,
scope, allowed value, amount and message of the error.

**Argument mode.** Given an operation, the program runs that one request:

```sh
kalyx eval '1/3 + 1/6'
kalyx expand x '(x + 1)^5'
kalyx diff x 'x^3 - 2*x + 7'
kalyx eval '1/0'
```

```text
value⇥0⇥0⇥0⇥1/2
value⇥0⇥0⇥0⇥1 + 5*x + 10*x^2 + 10*x^3 + 5*x^4 + x^5
value⇥0⇥0⇥0⇥-2 + 3*x^2
error⇥0⇥0⇥0⇥DivisionByZero⇥0..3⇥-⇥-⇥-⇥-⇥division by zero
```

The forms are `kalyx eval INPUT`, `kalyx expand VARIABLE INPUT` and
`kalyx diff VARIABLE INPUT`. Quote the input for the shell. The option
`--limits`, given before the operation, changes the limits of the request:

```sh
kalyx --limits max_exponent=256 expand x 'x^257'
```

```text
error⇥0⇥0⇥0⇥ResourceLimit⇥2..5⇥Field(max_exponent)⇥-⇥256⇥Required(257)⇥resource limit exceeded: max_exponent
```

**Line mode.** Without arguments, the program reads requests from standard
input, one per line, and writes one line for each, in order, as soon as it
is computed. A line holds the operation, the variable, the input and,
optionally, the limits, separated by tabs:

```sh
printf 'eval\tx\t2^64\nexpand\ty\t(y - 1)^3\ndiff\tx\t(x^2 + 1)^2\n' | kalyx
printf 'expand\tx\t(x + 1)^300\tmax_exponent=256\n' | kalyx
```

```text
value⇥0⇥0⇥0⇥18446744073709551616
value⇥0⇥0⇥0⇥-1 + 3*y - 3*y^2 + y^3
value⇥0⇥0⇥0⇥4*x + 4*x^3
error⇥0⇥0⇥0⇥ResourceLimit⇥8..11⇥Field(max_exponent)⇥-⇥256⇥Required(300)⇥resource limit exceeded: max_exponent
```

Limits are `-` for the defaults or `field=value` settings separated by `;`,
such as `max_work=1000000;max_depth=32`, with the field names of `Limits`.
The [command-line forms](docs/semantics.md#the-command-line-program) state
the forms, the line format and the rules for invalid lines.

**Exit status.**

| Status | Meaning |
| --- | --- |
| 0 | Every request gave a value, or `--version` or `--help` was written. |
| 1 | Some request ended with an error, written as its error line, or its value did not fit the limits of the request and has no line. |
| 2 | A usage error: arguments that the program does not accept, or a line of line mode that is not a request. Nothing is written for it on standard output. |
| 3 | Reading standard input or writing standard output failed, for example because the reader of a pipe closed it. The program stops at once. |

In line mode the status is the highest status of its lines. Diagnostics
go to standard error, prefixed with `kalyx:`.

## Limitations

This version is the first slice of the library. It does not have:

- rational functions: `expand x '1/x'` fails with `NotPolynomial`;
- factorization;
- multivariate polynomials: `expand` and `diff` work in one variable, and
  `expand x 'x*y'` fails with `UnknownSymbol`;
- function calls such as `sin(x)` and constants such as `pi`: both fail
  with `Unsupported`;
- floating point: every number is an exact rational;
- a REPL, sessions, variables and commands beyond `eval`, `expand` and
  `diff`: line mode answers each line on its own.

The program reads one line into memory at a time and does not bound the
length of a line before it reads it; the request then checks the input
against `max_input_bytes`.

## Rules the library is built to

`cargo xtask check`, which continuous integration runs, enforces the parts of
these rules that can be checked mechanically: forbidden `unsafe` code and
floating-point arithmetic, the interfaces and functions the library may not
use, the standard library interfaces it may use, and its dependencies and
license. It does so with the compiler, Clippy and a guard over the source,
the lock file and the manifest; [CONTRIBUTING](CONTRIBUTING.md#checks)
describes the checks and their limits.

- Values stay exact unless an operation explicitly computes an enclosure or an
  approximation; the library code forbids `unsafe` code and denies
  floating-point arithmetic until the machine floating-point path is added.
- Every request will run under explicit limits, a deadline and cancellation,
  checked cooperatively; the library uses no threads, hash containers,
  wall-clock time, thread-local state or unwinding recovery, and no
  transcendental functions of the platform math library.
- Library code uses only the standard library interfaces listed in
  [guard/std-paths.txt](guard/std-paths.txt). Its only direct third-party
  dependencies are num-bigint, num-rational and num-traits, for
  arbitrary-precision integers and rationals; adding one is a reviewed change
  of its own.
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

- [Architecture](docs/architecture.md): the planned components with their
  verification tiers and first callers, and the design rules of the
  foundations: term representation, coefficient fields, the context and
  error kinds. Of the library components, only the errors and result
  states, the context and limits, the exact numbers with the
  coefficient-field trait, the term core, the parser, the univariate
  polynomials, the function registry and the command entry are implemented
  yet.
- [Input syntax and semantics](docs/semantics.md): the one grammar of the
  library's input, its precedence and lexical rules, how an expression
  becomes a term, the output lines and the forms of the command-line
  program.
- [Public API conventions](docs/conventions/public-api.md): the rules that
  every public interface of the library is to follow.
- [Answer vectors](vectors/README.md): the format of the test vectors and
  their result kinds and limits.
- [Resource profile](docs/resource-profile.md): the heap and the stack that
  the requests of the answer vectors and deep inputs use, measured on one
  host, with the commands that measure them.
- [Formal verification](docs/formal-verification.md): the proof tooling
  taken over from krepi, its commands, the module list of the proof-target
  modules and the CI job of the proof gate; nothing is proved yet.
- Rules for this repository: [AGENTS](AGENTS.md) and
  [CONTRIBUTING](CONTRIBUTING.md); code taken over from the earlier
  implementation and from krepi: [PORTING](PORTING.md).

The rest of the library documentation (the semantics of further operations,
feature documents, subject domains and validation) is added as each part is
built.

## License

kalyx is released under the [MIT License](LICENSE). Copyright (c) 2026 The
casξ Authors; see [AUTHORS](AUTHORS). The patch of Aeneas in
`verification/tooling/` keeps its
[Apache License 2.0](verification/tooling/LICENSE-Apache-2.0).
