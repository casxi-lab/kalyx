# Answer vectors

`r02.tsv` holds the 58 answer vectors for kalyx 0.1, the planned first
release: parsing, exact rational arithmetic, and expansion and differentiation
in $\mathbb{Q}[x]$. They were converted mechanically from two fixtures of the
earlier implementation, without running any of its code; the file header
names the sources. The vectors are test data: `tests/vectors.rs` checks their
format today; replaying them against the library is planned together with the
command entry.

## Format

The file is UTF-8 text with one case per line and tab-separated columns. Lines
that start with `#` and empty lines are skipped. Every case has these seven
columns, none of them empty:

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
