# Answer vectors

`r02.tsv` holds the 58 answer vectors for kalyx 0.1, the first release:
parsing, exact rational arithmetic, and expansion and differentiation in
$\mathbb{Q}[x]$. They were converted mechanically from two fixtures of the
earlier implementation, without running any of its code (see
[Sources](#sources)). The vectors are test data: `tests/vectors.rs` checks
their format, and `tests/syntax.rs` replays the 32 cases that the parser
decides alone: the 31 evaluations, among them the depth, bit, syntax, division
and exponent cases, and the exponent limit of the expansion `degree_limit_1`,
which fails as its input is read; every error among them is checked with its
span. `tests/polynomials.rs` replays the 27 expansions and derivatives, each
as one request of the parser and the polynomials under its limits, and
compares its result with the answer by canonical form. `tests/command.rs`
replays all 58 through the command entry, each as one request under the limits
that its `limits` column sets: `compare_case` compares an answer by canonical
form, reading the answer and comparing the two terms by structure, and an
error by its kind and, for `ResourceLimit`, by the limit identifier of the
field that its limits set; it never compares display text or work, and a
negative test shows that it rejects a corrupted expectation. `tests/cli.rs`
replays all 58 through the line mode of the command-line program, each line
with the operation, variable, input and limits of its case, and compares the
output with the lines of the command entry byte for byte. The allocation check
in `checks/allocation/` runs each of the 58 cases 100 times under a counting
allocator and checks that every run leaves no memory behind; the [resource
profile](../docs/resource-profile.md) records the heap and the stack of each
case.

The six other files hold the full vectors of the earlier implementation: its
402 command-line cases, the inventory of its 968 integration tests,
12,573 observations of its library, two terminal sessions and the
1,782 outcomes of its root calls. They were exported in one run of that
implementation and record what it did, not answers that kalyx must give.
`tests/vectors.rs` checks the format of each file, and `tests/slices.rs`
replays the rows of the slices whose commands kalyx has today and counts the
rows of the pending slices. [Full vectors](#full-vectors) states where the
files come from, how their fields are written, how their values map to kalyx
and how the tests read them.

## Format

`r02.tsv` is plain TSV: UTF-8 text with tab-separated columns, no comment
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
| `Syntax`, `UnknownSymbol`, `DivisionByZero`, `NonIntegerExponent`, `NotPolynomial`, `Unsupported`, `Internal`, `OutsideDomain` | Faults of the input or of the library; no case of `r02.tsv` names `OutsideDomain`, which the integer kernel reports and no operation of these cases reaches. |

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

## Full vectors

### Provenance

The six files below were produced by an independent generator, which is not
public: an export tool that built
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78` with Rust 1.99.0 and
wrote the files in one run. It recorded the outputs of the command-line
cases, the library requests and the root calls, and executed the cases and
the requests twice, with the same outputs both times; it listed the
integration tests from the source, with their outcomes in that run; and it
converted the two recorded terminal sessions of the earlier implementation
(see [Terminal sessions](#terminal-sessions)).
The paths of files of the earlier implementation in this section, such as
`tests/interface/cases`, are paths in that tree, and a column that names such
a file writes `cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:<path>`.

The program name of the earlier implementation is written `cas-project`
wherever the program printed it, which is in its usage text. Apart from this
name, the escaping, the outcomes written in kalyx's terms (see
[Kinds](#kinds)) and the words that name the scopes, the recorded outputs
are those that the earlier implementation wrote; the work that it counted,
other than through the budgets of `library.tsv`, and the messages of the
errors of its library requests and root calls are not recorded, and no row
was added or removed.

### Files

| File | Rows | One row per |
| --- | --- | --- |
| [`cli_cases.tsv`](cli_cases.tsv) | 402 | case of the command-line program, see [Command-line cases](#command-line-cases) |
| [`integration_tests.tsv`](integration_tests.tsv) | 968 | integration test, see [Integration tests](#integration-tests) |
| [`library.tsv`](library.tsv) | 12,573 | request to the library, see [Library observations](#library-observations) |
| [`terminal_session.tsv`](terminal_session.tsv) | 471 | input line of a terminal session, see [Terminal sessions](#terminal-sessions) |
| [`terminal_collections.tsv`](terminal_collections.tsv) | 35 | input line of a terminal session of collection values, see [Terminal sessions](#terminal-sessions) |
| [`root_calls.tsv`](root_calls.tsv) | 1,782 | root call, see [Root calls](#root-calls) |

### Escaping

The six files have the format of `r02.tsv`: UTF-8 text, tab-separated
columns, the header row first, no comment lines, no empty lines and no empty
field. Their fields can hold any text, such as the output of a command, so
every field of these files is escaped as the message of an
[output line](../docs/semantics.md#output-lines) is:

| Byte in the value | Written in the field |
| --- | --- |
| backslash | `\\` |
| tab | `\t` |
| line feed | `\n` |
| carriage return | `\r` |
| every other byte from `0x00` to `0x1F`, and `0x7F` | `\x` and two lowercase hexadecimal digits, such as `\x1b` |

Every other byte is written as it is, so UTF-8 text stays UTF-8. A field `-`
holds no value or the empty text, and a value that is exactly `-` is written
`\-`, which is valid only as a whole field. A backslash that starts none of
these escapes is a format error, so every value has one written form. A
reader splits a line at its tabs first and then decodes each field. A stream
is recorded exactly, with its final line feed: an output of the one line `3`
is written `3\n`.

A column that holds a list, `args` of `cli_cases.tsv` and `commands` of
`integration_tests.tsv`, joins its items with tabs before the field is
escaped, so the items are separated by `\t`; an empty list is `-`. An empty
item is the empty text between two separators, before the first one or after
the last one: `i\t--work\t` is the list of `i`, `--work` and an empty
argument. A list of one empty item cannot be written; it does not occur. The
`limits` column of `library.tsv` keeps the form of `r02.tsv`, `field=value`
settings separated by `;`. A yes-or-no column holds `yes` or `no`.

`r02.tsv` holds no backslash and no control character, and its fields `-`
mean no value, so it reads the same under this rule.

### Command-line cases

`cli_cases.tsv` holds the 402 cases of the command-line program of the
earlier implementation, one for each case file
`tests/interface/cases/<area>/<name>.toml`, in the order of their paths. For
each case the export ran the program with the arguments of its case file
and, for the 14 sessions of its line mode, with the standard input of the
case, and recorded the exit status and both output streams. Where a case
file accepts any text in an output, the row holds the text that the program
actually wrote.

```text
id	source	command	args	stdin	status	stdout	stderr	kind
```

| Column | Meaning |
| --- | --- |
| `id` | `<area>/<name>` of the case file. |
| `source` | The case file, as `cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/interface/cases/<area>/<name>.toml`. |
| `command` | The first argument, or `-` for the case without arguments. |
| `args` | The other arguments, as a list (see [Escaping](#escaping)), or `-` when there are none. |
| `stdin` | The standard input, or `-` when the case gives none or an empty one; the program then reads an empty input. |
| `status` | The exit status. |
| `stdout`, `stderr` | What the program wrote to each stream, exactly, or `-` for nothing. |
| `kind` | `-` for a session of the line mode; otherwise `ok` for status 0, `usage` for status 2, and else the kind in kalyx of the error that the program reported, or `unknown`; see [Kinds](#kinds). |

Each case ran under the default limits of the earlier implementation. The
arguments `--work N` set its work budget, `max_work`, to `N` of that
implementation's work units; when `N` is not 0, the outcome can depend on how
work is counted, as the budgets of the
[library observations](#library-observations) do.

### Integration tests

`integration_tests.tsv` lists the 968 integration tests of the earlier
implementation, one per line, in the order of `id`. They belong to nine test
binaries: algebra (150), core (56), environment (147), equations (106),
interface (23), linear_algebra (199), nonlinear (137), numerics (55) and
symbolic (95). The file is a list, not a set of answers: it says where each
test is, how it reaches the command-line program and whether it passed, not
what it asserts.

```text
id	file	module	test	category	commands	ignored	status	blob
```

| Column | Meaning |
| --- | --- |
| `id` | `<binary>::<module>::<test>`, the path of the test function in its test binary; `cargo test --test <binary> -- --exact <module>::<test>` runs exactly this test. |
| `file` | The source file of the test, as `cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/<binary>/<file>.rs`. |
| `module` | The module of the test in its binary, as `cargo test` prints it before the test name. |
| `test` | The name of the test function. |
| `category` | `examples`, `properties`, `constructions`, `boundaries`, `resources` or `regressions` when the test sits in the submodule of that name directly below the module of its file, otherwise `-`. |
| `commands` | The first arguments that the test passes to the command-line program: its command words, `repl` for a session, and the options `--help`, `-h` and `--version`, each once and in code-point order, as a list (see [Escaping](#escaping)); `-` when the test does not run the program. Other first arguments, which the program rejects as usage errors, and the commands typed within a session or a `program` text are not listed. |
| `ignored` | `yes` for the 6 tests marked `#[ignore]`, otherwise `no`. |
| `status` | The result of one `cargo test` run of the nine binaries with Rust 1.99.0 in a debug build: `pass`, `fail`, or `ignored` for a test that the run skipped because it is marked `#[ignore]`. |
| `blob` | The Git blob SHA-1 of `file` at that commit. |

In that run 962 tests passed, 0 failed and the 6
tests marked `#[ignore]` did not run. The list was read from the source and
checked against the names that each test binary lists.

### Library observations

`library.tsv` holds 12,573 observations of the library of the
earlier implementation: a driver program linked against the library ran 93
inputs through five operations, four of them under each of four assumption
scopes, every request at several work budgets and once with a cancelled
token. The rows are its output in its order: by input in byte order, then
by scope (`none`, `real`, `pos`, `neg`) and operation (`simplify`, `parse`,
`expand`, `diff`, `ask`), then the full budget, the other budgets in
ascending order and the cancelled request.

```text
id	scope	operation	input	limits	cancelled	result	answer
```

| Column | Meaning |
| --- | --- |
| `id` | `i<NN>_<scope>_<operation>_w<budget>`, or `i<NN>_<scope>_<operation>_cancelled` for the cancelled request; `NN`, from `01` to `93`, is the position of the input in byte order. |
| `scope` | The assumption on `x`: `none`, no assumption; `real`, `x` is real; `pos`, `x` is positive; `neg`, `x` is negative. |
| `operation` | The operation of the earlier library; see the table below. |
| `input` | The input text in the syntax of the earlier implementation. |
| `limits` | `max_work=<budget>`, the only limit set on the request. |
| `cancelled` | `yes` when the request ran with a token cancelled before it started, otherwise `no`. |
| `result` | `ok`, or the outcome in kalyx's terms; see [Kinds](#kinds). |
| `answer` | For `ok`, the value as the earlier implementation displayed it: for `simplify`, the simplified expression; for `parse`, `expand` and `diff`, the function expression, followed by ` where <condition>` when its domain condition is not `true`; for `ask`, `true`, `false` or `unknown`. For any other result, `-`. |

Four of the operations correspond to one kalyx command each, which kalyx
does not have yet; `expand` corresponds to a kalyx command only for some
inputs:

| `operation` | What the earlier library did | kalyx command |
| --- | --- | --- |
| `simplify` | read the input as an expression and simplified it; only in the scope `none` | `simplify` |
| `parse` | read the input as a function expression under the scope | `fexpr` |
| `diff` | the same, then differentiated it once with respect to `x` | `f-diff` with the variable `x` and the order 1 |
| `ask` | the same, then asked whether it is positive | `f-ask` with the property `positive` |
| `expand` | the same, then expanded it | none in release 0.2: for the 8 inputs that denote a polynomial in $\mathbb{Q}[x]$ in the syntax of release 0.1, `(-x)^2`, `(x+x)^3`, `-x`, `-x^3`, `0`, `0^0`, `x` and `x+x-x`, the polynomial expansion `expand` of that release with the variable `x`; for the other inputs, a later release |

A scope maps to a literal scope operand of the kalyx command. Its written form
is fixed with the request form of these commands, in a later change; the file
names a scope only by the word in its `scope` column. The earlier command-line
program wrote the four scopes `{}`, `{x:real}`, `{x:positive}` and
`{x:negative}`.

For each input, scope and operation, the driver first ran the request with
`max_work=1000000` and read the work $n$ that it used; then once with each
budget of the set $\{0, 1, \lfloor n/2 \rfloor, n-1, n, n+1\}$, in ascending
order; then once more with `max_work=1000000` and a cancelled token. The
work units are those of the earlier implementation. Three groups of rows,
1,581 each, do not depend on how work is counted: the requests that were not
cancelled and had the budget 1000000, above the work of every request here;
those with the budget 0, which ended with `ResourceLimit`, since a request
charges work before it answers; and the cancelled requests, which ended with
`Cancelled` at their first charge. The other 7,830 rows
ran with the budget 1 or with a budget taken from the work $n$ that the
earlier implementation counted. kalyx charges work in its own units, so the
same `max_work` need
not end the same way in kalyx: such a row records the earlier outcome under
that budget, and another outcome in kalyx is a difference of the limit
mapping (see
[Limits of the earlier implementation](#limits-of-the-earlier-implementation)),
not a change of the row.

### Terminal sessions

`terminal_session.tsv` (471 rows) and `terminal_collections.tsv` (35 rows)
hold two recorded sessions of the interactive mode of the earlier
implementation, `cas-project repl`, taken from
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/data/interface/terminal_session.txt`
and
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/data/interface/terminal_collections.txt`.
The first was ported from an earlier test script of that implementation; the
expected replies of the second were calculated by hand. Each row is one input
line of the session, in its order, and the text that the terminal showed in
reply before the next prompt.

```text
id	input	output
```

| Column | Meaning |
| --- | --- |
| `id` | `line_N`, where `N` counts the input lines of the session from 1; the error messages of the session name the same number, as in `line 9: singular matrix has no inverse`. |
| `input` | The input line, without the prompt and the line end. |
| `output` | The reply: standard output and standard error together, as the terminal showed them, every line ended by a line feed, written `\n`. |

The rows of one file are one session: they run in order, in a session that
starts with no bindings, and the later rows depend on the bindings and on
the line numbers of the earlier ones. The last input, `:quit`, ends the
session; its output is the status line `session completed with errors`, and
the session exits with status 1 because of the deliberate errors before it.
The earlier implementation replayed both sessions in a pseudo-terminal and
compared every reply exactly; that replay passed at that commit, with Rust
1.99.0, in the run that exported these files. An input that ends with
`--work N` ran under that budget of the earlier implementation's work units,
as in [Command-line cases](#command-line-cases).

### Root calls

`root_calls.tsv` holds 1,782 calls, one for each combination of 2 scopes, 11
requests and 81 sources. The sources are roots of every degree around the
special cases 0, 1 and 2 and the limit 4096, roots inside other calls, powers,
conditions and held forms, degrees that are not unsigned integer literals, and
calls of the other elementary functions. The rows were written by the test
`functions::boundaries::root_calls_keep_the_outcomes_and_work_measured_on_main`
of
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/symbolic/functions.rs`,
run at that commit with its table writer enabled, in the order scope, request,
source; their scope, request and source agree row for row with
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:tests/data/symbolic/root_calls.tsv`.

```text
id	scope	request	source	result	answer
```

| Column | Meaning |
| --- | --- |
| `id` | `<scope>_<request>_<NN>`: the scope, the request in the short form of the table below, and the position of the source among the 81, from `01`. |
| `scope` | `none`: no assumptions; `real`: `x` is real. |
| `request` | One of the 11 requests below, run on the parsed source in the same context. |
| `source` | The input, parsed as a function expression under the scope. |
| `result` | `ok`, or the outcome in kalyx's terms of the error that the parse or the request ended with; see [Kinds](#kinds). |
| `answer` | For `ok`, the display of the result in the earlier implementation; for any other result, `-`. |

| Request | Short form | What it computes |
| --- | --- | --- |
| `parse` | `parse` | the parsed expression itself |
| `differentiate` | `differentiate` | the first derivative with respect to `x` |
| `series` | `series` | the series in `x` at 1, to order 3 |
| `limit 0+` | `limit_0_right` | the limit as `x` tends to 0 from above |
| `limit +inf` | `limit_pos_inf` | the limit as `x` tends to $+\infty$ |
| `integral` | `integral` | an antiderivative with respect to `x` |
| `approximate 2` | `approximate_2` | the numerical value at `x` = 2, with 53 bits and rounding to nearest, ties to even |
| `approximate -8` | `approximate_neg_8` | the same at `x` = -8 |
| `substitute -8` | `substitute_neg_8` | the exact substitution of -8 for `x` |
| `refine positive` | `refine_positive` | the expression refined under the fact that `x` is positive |
| `ask real` | `ask_real` | whether the value is real: `True`, `False` or `Unknown` |

The answer of an `approximate` request is the earlier implementation's record
of the approximation (such as its status, method, bits, enclosure, rounded
value and error bound), not an expression. Every request ran under the default
limits of the earlier implementation with a budget of 10,000,000 of its work
units; the work that each request used is not recorded.

### Kinds

The `kind` column of `cli_cases.tsv` and the `result` column of `library.tsv`
and `root_calls.tsv` name an outcome in kalyx's terms. The earlier
implementation had one enum of 25 error kinds; each maps as the [errors
contract](../docs/components/errors/contract.md#kinds-of-the-earlier-implementation)
fixes it:

| Earlier kinds | Value |
| --- | --- |
| `ResourceLimit`, `Cancelled`, `DeadlineExceeded` | the same names |
| `Syntax`, `DivisionByZero`, `UnknownSymbol`, `NotPolynomial`, `NonIntegerExponent` | the same names |
| `UnsupportedSymbolic`, `UnsupportedValue` | `Unsupported` |
| `NonConstantExponent` | `NonIntegerExponent` |
| `OutsideDomain` | the same name, a kind of kalyx since the integer kernel |
| `ContradictoryAssumptions`, `InvalidBinding`, `VariableMismatch`, `InvalidInterval` | the same names |
| `StaleEnvironment`, `DimensionMismatch` | the same names |
| `InvalidMatrix`, `SingularMatrix` | the same names |
| `FactorizationFailure`, `RootIsolationFailure` | `Internal`: every constructor of these kinds in the earlier implementation reports a failed self-check, so the state `NotApplicable` of a method that legitimately gives up does not occur |
| `InfiniteRoots` | `OutsideDomain` |
| `Indeterminate` | `Undecided`, a result state |
| `IntegrationFailure` | `Internal` for a failed check; `NotConverged`, a result state, for an initial sensitivity evaluation that misses its tolerance; `unknown` for an incomplete inner integration of a dynamic fit, whose outcome the contract leaves to the component that brings dynamic fitting |

A value is therefore `ok`, one of the 19 kalyx error kinds of this table,
one of the result states `Undecided` and `NotConverged`, or `unknown`;
`cli_cases.tsv` adds `usage` and `-`. A kind that kalyx adds in a later
release keeps its earlier name, so a row can name a kind before kalyx
defines it.

The library observations and the root calls recorded the earlier kind of
each error, so their `result` follows from the table. For
`FactorizationFailure`, `RootIsolationFailure` and `IntegrationFailure` it
is the value of the constructor whose message pattern, as in rule 5 below,
matches the message of the error, and `unknown` when none or several values
match. The command-line program printed only the message of an error and
its span, so the `kind` of a case follows from its arguments, its exit
status and its standard error, by the first of these rules that applies:

1. A session of the line mode, `repl` without other arguments, has no kind
   of its own and is `-`: each of its lines has its own outcome.
2. Status 0 is `ok`.
3. Status 2 is `usage`: a usage error of the program, which the library
   entry of kalyx does not have.
4. Any status other than 0, 1 and 2 is `unknown`.
5. For status 1, the message is the standard error without its final line
   feed and without a final ` at bytes N..M`. A message that is empty or has
   more than one line is `unknown`. Otherwise the message is matched as a
   whole against the patterns of the messages that the error constructors
   of the earlier implementation can build, read from its source: each `{...}`
   of a formatted message matches any text, and each pattern has the kind of
   its constructor. Of the patterns that match, those with the most literal
   characters decide, and their common value is the kind; if they have
   different values, or the value `unknown`, the kind is `unknown`. One
   message, `numeric divisor enclosure contains zero`, has two kinds,
   `DivisionByZero` for a point zero and `Undecided` otherwise, and is always
   `unknown`.
6. A message that no constructor builds but that the operand check of a
   command writes is `Syntax`; a message that matches nothing is `unknown`.

Of the 402 cases, 218 are `ok`, 45 `usage`, 14 `-` and 0 `unknown`; the other
125 have an error kind. `library.tsv` has 0 rows and `root_calls.tsv` 0 rows
whose `result` is `unknown`.

### Limits of the earlier implementation

The `Limits` of the earlier implementation had 24 fields. kalyx has nine and
derives every other bound from them, or takes it as an explicit parameter of
the request ([limits](../docs/components/context/contract.md#limits)). Each
earlier field maps to the kalyx field that bounds the same quantity, under
the same name or another, to the field that kalyx derives the bound from, or
to none:

| Earlier field | Default | kalyx field | Default | Mapping | Change |
| --- | --- | --- | --- | --- | --- |
| `max_input_bytes` | 65536 | `max_input_bytes` | 65536 | same | none |
| `max_parse_depth` | 128 | `max_depth` | 128 | renamed | The earlier nesting of calculation commands was bounded by the smaller of this field and 8; kalyx bounds nested commands by `max_frames`. |
| `max_nodes` | 8192 | `max_nodes` | 8192 | same | The earlier field also bounded numeric iterations; in kalyx an iteration bound is a parameter of its method, and reaching it is a result state. |
| `max_work` | 100000 | `max_work` | 100000 | same | kalyx charges its own amounts of work, so a budget set from the work of the earlier implementation has no fixed counterpart; see [Library observations](#library-observations). |
| `max_integer_bits` | 4096 | `max_integer_bits` | 4096 | same | kalyx also derives the bits of a working precision from it. |
| `max_exponent` | 4096 | `max_exponent` | 4096 | same | A 32-bit field before, 64-bit now. kalyx also derives degrees and orders of derivatives from it. |
| `max_degree` | 256 | `max_exponent` | 4096 | derived | Under the defaults a degree from 257 to 4096 is admitted. `max_exponent=256` reproduces the earlier bound and also bounds exponents by 256. |
| `max_terms` | 257 | `max_nodes` | 8192 | derived | A term is at least one node. Under the defaults up to 8192 one-node terms are admitted where 257 terms were. |
| `max_symbolic_depth` | 128 | `max_depth` | 128 | renamed | One depth for syntax, terms and values. |
| `max_symbolic_bytes` | 262144 | `max_storage_bytes` | 262144 | derived | Measured by kalyx's byte formulas; the bytes of an output, which the earlier field also bounded, are bounded by `max_output_bytes`. |
| `max_domain_conditions` | 64 | `max_nodes` | 8192 | derived | A condition is at least one node. Under the defaults up to 8192 one-node conditions are admitted where 64 were. |
| `max_environment_bindings` | 128 | none | | cannot map | Bindings of a session; no kalyx request holds a session yet. |
| `max_call_depth` | 32 | `max_frames` | 32 | renamed | The earlier field was also capped at 64. |
| `max_environment_nodes` | 65536 | `max_nodes` | 8192 | derived | The nodes of open frames and temporaries; the nodes of a stored session have no counterpart yet. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 65536 nodes, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |
| `max_environment_bytes` | 1048576 | `max_storage_bytes` | 262144 | derived | As `max_environment_nodes`, in bytes. Under the defaults kalyx admits 262144 bytes in all where the earlier field admitted 1048576 bytes, so a request that fitted before can end with `ResourceLimit` on `max_storage_bytes`. |
| `max_factor_cells` | 65536 | `max_nodes` | 8192 | derived | Temporaries of factorization. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 65536 cells, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |
| `max_root_cells` | 65536 | `max_nodes` | 8192 | derived | Temporaries of real root isolation. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 65536 cells, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |
| `max_matrix_dimension` | 256 | none | | cannot map | A size without elements is an explicit parameter of the request, reported by its name. |
| `max_matrix_cells` | 65536 | `max_nodes` | 8192 | derived | A cell is at least one node. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 65536 cells, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |
| `max_matrix_scratch_cells` | 131072 | `max_nodes` | 8192 | derived | Temporaries of elimination. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 131072 cells, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |
| `max_sparse_dimension` | 1000000 | none | | cannot map | As `max_matrix_dimension`. |
| `max_sparse_nnz` | 65536 | `max_nodes` | 8192 | derived | An entry is at least one node. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 65536 entries, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |
| `max_sparse_bytes` | 8388608 | `max_storage_bytes` | 262144 | derived | Bytes of sparse storage. Under the defaults kalyx admits 262144 bytes in all where the earlier field admitted 8388608 bytes, so a request that fitted before can end with `ResourceLimit` on `max_storage_bytes`. |
| `max_sparse_fill` | 131072 | `max_nodes` | 8192 | derived | Temporaries of sparse elimination. Under the defaults kalyx admits 8192 nodes in all where the earlier field admitted 131072 cells, so a request that fitted before can end with `ResourceLimit` on `max_nodes`. |

`max_output_bytes` has no earlier field. The earlier implementation also
capped some fields by constants: the parse depth by 256 in expressions and
algebraic literals, by 128 in function expressions, programs and algebraic
literals and by 64 in user functions and programs; the symbolic depth by 128
in terms, function expressions, definite integrals and sparse operators and
by 64 in user functions; the call depth by 64; the nesting of calculation
commands by 8; and the exponents and orders of power series by 268435455.
kalyx applies every field as it is given.

The limit of a row maps through this table. For a field marked `same` or
`renamed`, other than `max_work`, whose units differ, the kalyx field set to
the earlier value bounds the same quantity, so a row that exceeded such a
field carries its setting over. A row that ran under the earlier defaults and
reached a derived field whose default differs, a field that cannot be mapped
or one of the caps above ran under a bound that kalyx does not have, and a row
that fitted a larger earlier default of a derived field can exceed the smaller
default of kalyx; the file keeps its outcome as observed. `cli_cases.tsv` and
the terminal sessions have no `limits` column: they ran under the default
limits, with `max_work=N` where an input sets `--work N`. `root_calls.tsv` ran
under the default limits with `max_work=10000000`; of its 82 `ResourceLimit`
rows, the 66 that exceed the root degree and the 4 that exceed the integer
bits have the same default in kalyx (`max_exponent` and `max_integer_bits`,
4096), and the 12 that exceed the numeric root degree, the earlier degree
bound 256, ran under a default that kalyx does not have.

### Format checks

`tests/vectors.rs` runs five checks on each of the six files, in this order:

1. Plain TSV: UTF-8 text in lines that each end with a line feed, with no
   empty line, no line that starts with `#` and no empty field, and every
   field written as [Escaping](#escaping) states: no control byte is
   written as it is, and every backslash starts an escape.
2. The header row: the first line names the columns of the file, as the
   sections above give them.
3. The columns: every row has as many fields as the header row.
4. The ids: no value occurs twice in the `id` column, the first one.
5. The rows: the file has the number of rows of the table in
   [Files](#files).

A negative test for each check corrupts a copy of each of the six files in
memory and shows that the check rejects it.

### Slice replay

A slice is the part of the full vectors that one capability of kalyx
answers. `tests/slices.rs` holds the table of the slices. Each names the
commands of its command-line cases, by the `command` column of
`cli_cases.tsv`; the requests of its root calls, by the `request` column of
`root_calls.tsv`; and the operations of its library observations, by the
`operation` column of `library.tsv`, each with its kalyx command from the
table of [Library observations](#library-observations) and the inputs that
the slice takes, where it does not take all of them. Each slice also states
the number of rows that it selects in each of the three files, and no row is
in two slices. Three kinds of rows belong to no slice, and the test neither
replays them nor counts them as pending: the sessions, which are the cases
of the line mode, whose command is `repl`, and the two terminal sessions;
the integration tests, which list tests and record no answers; and the rows
of the commands, requests and inputs that no slice names. These are the
227 other command-line cases, among them those of `program`, `cancel`,
`solve` and `matrix`; the 2,720 `expand` observations of the 85 inputs other
than the eight polynomial inputs; and the 810 root calls of the requests
`limit 0+`, `limit +inf`, `integral`, `approximate 2` and `approximate -8`.
A test checks these numbers.

A slice is enabled when the dispatch table of the command entry registers
every command that it names. The test reads this from the command entry,
which fails a request whose operation the table does not hold with
`Unsupported`, without a span and before any work. The other slices are
pending: the test counts their rows, prints the counts and checks them, and
replays none of them. The test reads the three files once and replays the
rows of an enabled slice, each row that it runs as one request through
`execute`:

- A command-line case takes the input of the request from its arguments,
  the variable from `--var NAME`, or `x` without it, and runs under the
  default limits, with `max_work=0` for `--work 0`. Its expectation is its
  `kind` and, for `ok`, its standard output without the final line feed. A
  case with the kind `usage` is not compared, since the library entry has no
  usage error, and neither is a case with `--work N` for an `N` other than
  0.
- A library observation runs the kalyx command of its operation on its
  input, with the variable `x`: the budget 1000000 under the default limits,
  the budget 0 under `max_work=0`, and the cancelled request under the
  default limits with its flag cancelled before the request starts. The
  rows under the other budgets, which depend on how the earlier
  implementation counted work, are not compared. A row that needs an
  operand which no request has yet is reported as a difference without
  running: a row in a scope other than `none`, which needs a scope operand,
  and a row of `diff` or `ask`, whose command also takes the order 1 or the
  property `positive`. The polynomial expansion takes no scope operand,
  since a scope assumes a property of `x`, which does not change a
  polynomial, so its rows in all four scopes are the same request.
- No request has the form of a root call yet, so a root call of an enabled
  slice is reported as a difference.

The comparison is the one of `r02.tsv`: a row that is `ok` needs a value
equal by canonical form to its answer, read with `parse`; a result state
needs the same state; and an error needs the same kind and, for a
`ResourceLimit` under `max_work=0`, the field `max_work`. Display text and
work are never compared, and a row whose outcome kalyx does not define is a
difference. A negative test corrupts, each in a copy of its file, the answer
of a library observation, the kind of a command-line case and the outcome of
a cancelled request, and shows that each gives exactly one difference, at
its row; another shows that a row that needs a scope, a property or an order
is a difference.

| Slice | Commands | Root-call requests | Library operations | Rows: cases, observations, root calls | State |
| --- | --- | --- | --- | --- | --- |
| `exact_numbers` | `eval` | | | 9, 0, 0 | enabled: 7 compared, 2 usage errors |
| `polynomials` | `expand`, `diff` | | `expand` on the eight inputs of [Library observations](#library-observations) | 5, 256, 0 | enabled: 101 compared, 160 under other budgets |
| `function_expressions` | `fexpr`, `simplify` | `parse` | `parse`, `simplify` | 7, 3,645, 162 | pending |
| `questions_and_refinement` | `f-refine`, `ask`, `f-ask` | `refine positive`, `ask real` | `ask` | 3, 2,976, 324 | pending |
| `substitution` | `f-subs`, `subs`, `at` | `substitute -8` | | 20, 0, 162 | pending |
| `function_derivatives` | `f-diff`, `rat-diff` | `differentiate` | `diff` | 6, 2,976, 162 | pending |
| `series` | `f-series` | `series` | | 2, 0, 162 | pending |
| `univariate_polynomials` | `compose`, `discriminant`, `divrem`, `gcd`, `gcdex`, `resultant`, `squarefree` | | | 16, 0, 0 | pending |
| `univariate_factorization` | `factor`, `apart` | | | 7, 0, 0 | pending |
| `multivariate_polynomials` | `mdiff`, `mdiv`, `mfactor`, `mgcd`, `mp-at`, `mpoly`, `msubs`, `poly-ring` | | | 17, 0, 0 | pending |
| `real_roots` | `roots`, `count-roots`, `refine` | | | 12, 0, 0 | pending |
| `real_algebraic_numbers` | `alg`, `alg-root`, `radical`, `alg-compare`, `minpoly`, `alg-at` | | | 12, 0, 0 | pending |
| `complex_algebraic_numbers` | `complex`, `complex-at`, `complex-equal`, `complex-imag`, `complex-minpoly`, `complex-real`, `complex-root`, `complex-roots`, `conjugate`, `norm2`, `principal-root` | | | 19, 0, 0 | pending |
| `number_fields` | `field-element`, `field-value`, `number-field` | | | 6, 0, 0 | pending |
| `real_sets_and_inequalities` | `contains`, `ineq`, `interval`, `rel-and`, `rel-not`, `rel-or`, `set`, `set-complement`, `set-difference`, `set-intersect`, `set-union` | | | 19, 0, 0 | pending |

The two enabled slices hold the commands of release 0.1, and their rows
replay without a difference. The 13 pending slices hold 146 command-line
cases, 9,597 library observations and 972 root calls, and name commands
that kalyx does not have yet.
