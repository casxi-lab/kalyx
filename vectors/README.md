# Answer vectors

`r02.tsv` holds the 58 answer vectors for kalyx 0.1, the planned first
release: parsing, exact rational arithmetic, and expansion and differentiation
in $\mathbb{Q}[x]$. They were converted mechanically from two fixtures of the
earlier implementation, without running any of its code (see
[Sources](#sources)). The vectors are test data: `tests/vectors.rs` checks
their format, and `tests/syntax.rs` replays the 32 cases that the parser
decides alone: the 31 evaluations, among them the depth, bit, syntax,
division and exponent cases, and the exponent limit of the expansion
`degree_limit_1`, which fails as its input is read; every error among them is
checked with its span. `tests/polynomials.rs` replays the 27 expansions and
derivatives, each as one request of the parser and the polynomials under its
limits, and compares its result with the answer by canonical form.
`tests/command.rs` replays all 58 through the command entry, each as one
request under the limits that its `limits` column sets: `compare_case`
compares an answer by canonical form, reading the answer and comparing the
two terms by structure, and an error by its kind and, for `ResourceLimit`,
by the limit identifier of the field that its limits set; it never compares
display text or work, and a negative test shows that it rejects a corrupted
expectation. `tests/cli.rs` replays all 58 through the line mode of the
command-line program, each line with the operation, variable, input and
limits of its case, and compares the output with the lines of the command
entry byte for byte. The allocation check in `checks/allocation/` runs each
of the 58 cases 100 times under a counting allocator and checks that every
run leaves no memory behind; the
[resource profile](../docs/resource-profile.md) records the heap and the
stack of each case.

## Format

The file is plain TSV: UTF-8 text with tab-separated columns, no comment
lines and no empty lines, so that any TSV reader, including the file view on
GitHub, takes the first line as the header. The first line is the header row,
which names the seven columns in order:

```text
id	operation	variable	input	result	answer	limits
```

Every following line is one case with these seven columns, none of them
empty:

| Column | Meaning |
| --- | --- |
| `id` | A unique name of the case. |
| `operation` | `eval` evaluates the input to an exact rational number; `expand` expands it as a polynomial in `variable`; `diff` expands it and differentiates with respect to `variable`. |
| `variable` | The polynomial variable. `eval` cases also name one, which they do not use. |
| `input` | The input text in the library's syntax. |
| `result` | `ok`, or the error kind that the request must end with (see below). |
| `answer` | For `ok`, the expected answer in the library's syntax; it is to be compared by canonical form, not as text. For an error, `-`. |
| `limits` | `-` for `Limits::default()`, or `field=value` settings separated by `;`, applied on top of the defaults. |

Of a request's outcome, a vector records only the result kind and, for `ok`,
the answer. Display text, work units and the resource profiles of the earlier
fixtures are not recorded.

## Sources

The first 11 cases come from
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:fixtures/workloads.tsv`
and the other 47 from
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:fixtures/profiles.tsv`,
two fixtures of the earlier implementation, in their order there. The
expected values of the 47 profile cases were computed by an independent
generator with exact integer and rational arithmetic (seed 212148262); the
generator is not public. The 11 workload cases are small identities that can
be checked by hand; their expected values are taken as written.

## Result kinds

The `result` column takes one value from this fixed table:

| Value | Class |
| --- | --- |
| `ok` | The request returns an answer. |
| `ResourceLimit`, `Cancelled`, `DeadlineExceeded` | Request failures raised by the context. |
| `Syntax`, `UnknownSymbol`, `DivisionByZero`, `NonIntegerExponent`, `NotPolynomial`, `Unsupported`, `Internal` | Faults of the input or of the library. |

The error kinds of the earlier implementation that occur in these cases keep
their names: `Syntax`, `UnknownSymbol`, `DivisionByZero`,
`NonIntegerExponent`, `NotPolynomial` and `ResourceLimit`. In general, its
`UnsupportedSymbolic` and `UnsupportedValue` map to `Unsupported`, and
`NonConstantExponent` maps to `NonIntegerExponent`; none of the three occurs
here. A case whose earlier kind has no counterpart in this table would not be
converted.

## Limits

The `limits` column names `Limits` fields. Each `ResourceLimit` case states
the limit it exceeds, so it does not depend on a default value:

| Case | Limit | What exceeds it |
| --- | --- | --- |
| `degree_limit_1` | `max_exponent=256` | the exponent 257 |
| `bit_limit_1` | `max_integer_bits=4096` | $2^{4096}$, which has 4097 bits |
| `depth_limit_1` | `max_depth=128` | 192 nested parentheses |
| `right_depth_limit_1` | `max_depth=32` | 64 right-nested sums in parentheses |

`max_depth=32` for `right_depth_limit_1` is below the default of 128 (of
`Limits` and of the earlier implementation), so that 64 right-nested sums
exceed it however nesting depth is counted.
