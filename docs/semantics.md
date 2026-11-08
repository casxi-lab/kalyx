# Input syntax and semantics

This document states the one grammar of the input of kalyx, the text of an
expression that a request gives to the library, and how that text becomes a
term of the [term core](components/terms/contract.md). The parser,
`kalyx::syntax::parse` (also `kalyx::parse`), reads it. Its
[contract](components/syntax/contract.md) states the limits of the parser
with their measures, its charges, its spans and errors, and its tests. The
section [output lines](#output-lines) states the bytes of the one output
format of the library, the line that the command entry writes for the
outcome of a request, and the last section,
[the command-line program](#the-command-line-program), the forms of the
program `kalyx`, its line format and its exit statuses.

**Status.** The grammar of this release reads numbers, identifiers, the binary
operators `+`, `-`, `*`, `/` and `^`, parentheses and unary minus, and is
implemented in `src/syntax.rs` and `src/syntax/`. Later releases extend it as
[the single-grammar rule](#the-single-grammar-rule) states. The output lines
are implemented in `src/command/line.rs`, and the command-line program in
`src/main.rs`.

## The single-grammar rule

kalyx has one input grammar. Every expression that the library reads is read
by this grammar, and a feature that needs more syntax extends this grammar; it
never writes a scanner or a parser of its own. An extension only adds
productions for input that the grammar rejects, and never changes the meaning
or the canonical form of input that the grammar accepts: an input accepted by
this release reads the same in every later release. For this reason the
reserved names, function-call syntax, juxtaposition and the number literals
beyond the forms `1` and `1.5` are errors today, so that later releases can
give them a meaning.

The rule covers the text of expressions. The arguments of the command-line
program and the tab-separated fields and limits of its input lines frame a
request around that text and are outside the grammar; see
[the command-line program](#the-command-line-program).

## Grammar

The grammar in ISO EBNF, where `,` is concatenation, `|` alternation,
`{ ... }` repetition, `[ ... ]` an option and `? ... ?` a set described in
words:

```text
input      = expression ;
expression = term , { ( "+" | "-" ) , term } ;
term       = unary , { ( "*" | "/" ) , unary } ;
unary      = "-" , unary | power ;
power      = primary , [ "^" , unary ] ;
primary    = number | identifier | "(" , expression , ")" ;
number     = digit , { digit } , [ "." , digit , { digit } ] ;
identifier = ( letter | "_" ) , { letter | digit | "_" } ;
letter     = ? an ASCII letter, "A" to "Z" or "a" to "z" ? ;
digit      = ? an ASCII digit, "0" to "9" ? ;
```

The [lexical rules](#lexical-rules) below add what the productions do not
show: where whitespace may stand, how far a number literal extends, the
reserved names and function-call syntax.

### Precedence and associativity

From the tightest binding to the loosest:

| Operators | Associativity | Examples |
| --- | --- | --- |
| Parentheses | grouping | `(1+2)*3` is 9 |
| `^` | right | `2^3^2` is $2^9 = 512$; `(2^3)^2` is 64 |
| unary `-` | prefix | `-2^2` is $-4$; `(-2)^2` is 4; `-3^2*2` is $-18$ |
| `*`, `/` | left | `8/4/2` is 1; `2/3*3` is 2 |
| `+`, `-` | left | `5-2-1` is 2 |

So `-2^2 + 2^3^2` is $-4 + 512 = 508$.

- **Unary minus.** A unary minus binds less tightly than `^` and more tightly
  than `*` and `/`. It may start every operand: the input, the contents of
  parentheses, the operand after a binary operator and the operand of another
  unary minus. So `2*-3+4` is $-2$, `1--1` is 2 and `--2` is 2.
- **Unary minus after `^`.** It may follow `^`: the exponent of a power is a
  `unary`, which may itself be a power. So `2^-2` is $2^{-2} = 1/4$, `-2^-2`
  is $-1/4$, and `2^-1^2` is $2^{-(1^2)} = 1/2$.
- **No unary plus.** `+1` and `1++2` are syntax errors.

### Lexical rules

- **Characters and whitespace.** The input is UTF-8 text, and every token is
  ASCII. Whitespace, which is space, tab, line feed, form feed and carriage
  return, separates tokens and has no other meaning. Any other character that
  starts no token, such as a vertical tab, `=`, `,` or any character outside
  ASCII, is a syntax error with the span of the whole character: `1+λ` fails
  at bytes 2 to 4.
- **Number literals.** A number literal starts with a digit or a point, and
  the token runs over every ASCII letter, digit, `_` and point that follows
  without whitespace. The whole run is one literal, and in this release it
  must have the form of `number`: one or more digits, optionally followed by a
  point and one or more digits. `.5`, `1.`, `1e3`, `1.2.3`, `2x` and `1_000`
  are therefore each one literal that fails with a syntax error at its first
  character outside that form, or with an empty span at its end for `1.`;
  none of them is read as two operands. A sign is an operator, never part of
  a literal, so `1e-3` is the literal `1e`, a `-` and the literal `3`, and
  fails in its first literal, at the `e`. A literal is converted exactly, by
  the decimal literal function of the
  [exact numbers](components/numbers/contract.md#decimal-literals): its
  digits as an integer over $10^k$ for $k$ digits after the point, reduced,
  so `1.5` is $3/2$ and `0.1 + 0.2` is $3/10$.
- **Identifiers.** An identifier is an ASCII letter or `_`, followed by ASCII
  letters, digits and `_`: the rule of
  [symbol names](components/terms/contract.md#symbol-names) of the term core,
  which the parser shares with it. Identifiers are case-sensitive, and an
  identifier is the name of a symbol.
- **Reserved names.** `pi`, `i` and `undefined` are reserved for the constants
  $\pi$, $i$ and the undefined value of a later release. Where an operand is
  expected, they fail with `Unsupported` and the span of the name as soon as
  they are read, before the token after them, also when `(` follows: `pi(x)`
  fails with the span of `pi`. Names that only resemble them, such as `Pi`,
  `ii` or `pi2`, are ordinary identifiers. A later release takes the names of
  new constants only from this list or from spellings that are errors in this
  release.
- **Function-call syntax.** An identifier followed by `(`, with or without
  whitespace between them, is function-call syntax: `f(x)`, `f (x)` and
  `max(x, y)`. It is reserved for the function calls of a later release and,
  where an operand is expected, fails with `Unsupported` and the span from the
  start of the name to the end of the `(`, whatever follows it.

### What the grammar does not contain

- **Juxtaposition.** Two operands with no operator between them, such as
  `2 x`, `x y`, `2(x + 1)` or `(x + 1)(x - 1)`, are a syntax error at the
  second operand, also when it is a reserved name or function-call syntax:
  `1 pi` and `1 f(x)` fail with `Syntax` at `pi` and at `f`. A later release
  may read juxtaposition as multiplication.
  It will never split a number literal: the run of letters, digits, `_` and
  points that follows a digit stays one literal token, so `2x`, `1e3` and
  `1.5` are never read as the products `2*x`, `1*e3` or `1*.5`, and the
  number literals that a later release adds, `.5`, `1.` and scientific
  notation such as `1e-3`, keep their meaning.
- **Command words.** The grammar has no command words. Operations such as
  evaluation, expansion and differentiation are chosen by the
  [command entry](components/command/contract.md), by the name of the
  operation that a request gives apart from its input, before it gives the
  input to `parse`. Inside an expression, a word such as `eval`, `expand` or
  `diff` is an ordinary identifier, so `diff` is the symbol named `diff`,
  and `diff(x)` is function-call syntax.
- **Other notation.** Unary plus, `**`, comparisons, assignments, commas,
  brackets and operators outside ASCII are not part of the grammar and are
  syntax errors.

## From syntax to terms

The parser reads the whole input first, and only then builds the term, so
every syntax error and every limit of the parser is reported before any term
is built. The term is then built through the constructors of the term core,
which keep it in canonical form:

| Syntax | Term |
| --- | --- |
| a number literal | `Term::number` of its exact value |
| an identifier | `Term::symbol` of its name |
| `-a` | `a.negate()`, the product of $-1$ and $a$ |
| a chain `a + b - c` | `Term::sum` of $a$, $b$ and $-c$: every operand after a `-` is negated first, which is `a.subtract(c)` |
| a chain `a * b / c` | `Term::product` of $a$, $b$ and $c^{-1}$: every operand after a `/` is raised to the power $-1$ first, which is `a.divide(c)` |
| `a ^ e` | `a.power(k)`, where $e$ is the integer constant $k$ |
| `( a )` | $a$ |

- **Order.** Operands are built before their operation, from left to right,
  and the first failure ends the request. In a chain, the operand after a
  `-` is negated, and the operand after a `/` raised to the power $-1$, as
  soon as it is built and before the next operand is, as in the
  left-associative reading of the chain: `1/0 + x^y` and `1/0*x^y` fail with
  `DivisionByZero`, while `x^y + 1/0` and `x^y*1/0` fail with
  `NonIntegerExponent`. The sum or the product of a whole chain is then built
  by one call of the term core, so a long sum or product is sorted and merged
  once, not once per operator.
- **Exponents.** The exponent of a power is built after its base and before
  the power, so `(1/0)^(1/0)` fails at the division of its base. It must be a
  number that is an integer; otherwise the power fails with
  `NonIntegerExponent`, the exponent is not an integer constant, with the span
  of the exponent and its parentheses: `2^(1/2)`, `x^0.5`, `x^y` and
  `x^(x/x)`. Since the exponent is canonical, `x^(1+1)` is $x^2$ and
  `x^(x-x)` is $x^0 = 1$. The integer becomes an `i64` under the exponent
  rules of the term core: a magnitude beyond `max_exponent` or beyond
  $2^{63} - 1$ fails with `ResourceLimit` naming `max_exponent`, also with
  the span of the exponent.
- **Strict numeric evaluation.** Numbers are evaluated exactly as their terms
  are built, so an invalid numeric subterm fails at once and cannot be
  absorbed by the term around it. `0*(1/0)` and `(1/0)^0` fail with
  `DivisionByZero` at the division `1/0`, `0^(-1)` and `0^-1` at the power,
  and `x/(x-x)` at the division, because $x - x$ is 0; `0^0` is 1. Terms are
  not simplified beyond their canonical form, so `x/x` is $x \cdot x^{-1}$,
  not 1, while `x - x` is 0.

## Reading display text back

The [display text](components/terms/contract.md#display) of every term that
the constructors of this release build is input of this grammar that reads
back as the same term, so display text can be given to `parse` again:

- a number is its integer or fraction, `-3/4`, which reads as $-3$ divided
  by 4, since a unary minus binds more tightly than `/`;
- a negative exponent is written in parentheses, `x^(-1)`, and a base that
  is not a symbol is in parentheses, `(x + y)^(-2)` and `(x^(-1))^0`;
- a product writes its coefficient first, `1/2*x^(-1)*y^(-1)` or `-z*(x + y)`,
  which reads from the left as $\frac{1}{2} \cdot x^{-1} \cdot y^{-1}$, and a
  sum among its factors in parentheses;
- a sum writes its constant first and its monomials after ` + ` or ` - `,
  `-3/4 + x - 1/2*y`, and keeps a witness monomial with the coefficient 0,
  `5 + 0*x^(-1)`, which reads back as the same witness.

The display grammar also has a reserved form for calls, `f(a, b)`. No
constructor of this release builds a call, so no display text of this release
holds one; the form is function-call syntax, which fails with `Unsupported`
until calls arrive and the grammar adds them.

Display text is read under the limits of the request like any other input,
and it can need more than its term. Its syntax depth can exceed the depth of
its term. It has more syntax nodes than its term has nodes: `x^(-1)` is a
term of two nodes and has four syntax nodes, and a monomial of a sum such as
` - 2/3*x^2` has eight syntax nodes, while it adds two nodes to the term of
the sum, the power and the symbol, since the sum holds its coefficient. So
the display of $\sum_{k=1}^{1100} -\frac{k}{k+1} x^k$, a term of 2,200
nodes, has more than 8,192 syntax nodes, the default `max_nodes`. And a
literal is bounded by 4 bits per decimal digit, so a number with more than
about 83 percent of `max_integer_bits` bits in its numerator or its
denominator is read back only under a larger `max_integer_bits`. The text of
a term near these limits therefore reads back only under a larger
`max_depth`, `max_nodes` or `max_integer_bits`, and reading it charges work
like any other input.

## Limits

The parser checks the length of the input against `max_input_bytes` before it
reads it, compares the nesting of the input with `max_depth` while it reads,
and checks the number of its syntax nodes with `check_storage` at scope
`Value`, so against `max_nodes`. The [contract](components/syntax/contract.md)
defines the measures. In short, the whole input is at level 1, and one level
deeper are the contents of parentheses, the operand of a unary minus, the
exponent of a power and every operand of a chain after its first, so
`1+2+3` has the depth 2, a tower `2^3^4` the depth 3 and 127 nested
parentheses around a number the depth 128; and a syntax node is a number, an
identifier, a unary minus or a binary operator, so parentheses add none.

## Output lines

The command entry writes the outcome of a request as one line of bytes with
`kalyx::command::serialize`. This line is the only output format of the
library: a program shows results only through it. The
[contract of the command entry](components/command/contract.md) states how
the line is charged and when it is written; this section states its bytes.

**Lines and fields.** A line is UTF-8 text: fields separated by one tab, the
byte `0x09`, and ended by one line feed, the byte `0x0A`. A line holds no
other tab, line feed or control character, since the text of a field that
could hold one is escaped. The first field names the kind of the line, and
the kind fixes the number of fields:

| First field | Fields |
| --- | --- |
| `value` | 5: `value`, the three versions and the text of the value |
| `state` | 5: `state`, the three versions and the name of the state |
| `error` | 11: `error`, the three versions, the kind, the span, the limit, the scope, the allowed value, the amount and the message |

Fields 2, 3 and 4 are the input version, the context version and the
settings version of the request, which the outcome echoes. A version, a
span offset, an allowed value and an amount are `u64` numbers, written in
decimal ASCII digits without a sign, separators or leading zeros, so zero is
`0`. The display text of a value is not such a number: it follows the term
core and may hold signs, fractions and integers of any size, such as `-2/3`.

**Value lines.** The fifth field is the display text of the term of the
result, as the [term core](components/terms/contract.md#display) writes it:
input of this grammar that [reads back](#reading-display-text-back) as the
same term. Display text holds only printable ASCII characters, so it is
written as it is. Results are compared with expected answers by their
canonical terms, never by this text.

**State lines.** The fifth field is the name of the mathematical state:
`NotConverged`, `Unevaluated`, `NotApplicable`, `Undecided` or
`IterationLimit`. No operation of this release ends in a state.

**Error lines.** The fields after the versions:

| Field | Bytes |
| --- | --- |
| Kind | `ResourceLimit`, `Cancelled` or `DeadlineExceeded` for a request failure; for a fault, the name of its kind: `Syntax`, `UnknownSymbol`, `DivisionByZero`, `NonIntegerExponent`, `NotPolynomial`, `Unsupported` or `Internal` |
| Span | `start..end`, the half-open range of byte offsets into the input of the request; `-` when the error has no span |
| Limit | for `ResourceLimit`, `Field(name)` with the name of a field of `Limits`, such as `Field(max_work)`, or `Parameter(name)` with the escaped name of a parameter of the request; otherwise `-` |
| Scope | for `ResourceLimit` on `max_nodes` or `max_storage_bytes`, where the limit was reached: `Value`, `Frame` or `Temporary`; otherwise `-` |
| Allowed | for `ResourceLimit`, the value of the limit in force; otherwise `-` |
| Amount | for `ResourceLimit`, `Used(n)`, `Required(n)` or `Bound(n)`: the total at the check, the amount needed, or an upper bound of it; otherwise `-` |
| Message | the English message of the error, escaped |

- **Kinds.** The kinds are the names of the `result` column of the
  [answer vectors](../vectors/README.md#result-kinds). A kind that a later
  release adds is written by its name.
- **Spans.** A span counts bytes of the input text of the request, never of
  the operation or the variable. The errors of the parser, including the
  errors of the terms that it builds, have the spans that its
  [contract](components/syntax/contract.md#spans) states. An error that has
  no single range of the input has the span `-`: settings other than the
  default, an unknown operation, a variable that is not a symbol name, and
  every error of the work on a term after it is read, such as
  `UnknownSymbol`, `NotPolynomial` and the request failures of its charges,
  since a term has no span.
- **Limits.** The limit, the scope, the allowed value and the amount are
  those of the `LimitExceeded` record of the error.
- **Messages.** The message is text for people. Its bytes depend only on the
  error, so they are the same in every run, but its wording is not part of
  the interface and may change in a later release; programs read the other
  fields.

**Escaping.** In a message and in the name of a parameter, a backslash is
written `\\`, a tab `\t`, a line feed `\n`, a carriage return `\r`, and every
other byte from `0x00` to `0x1F` and the byte `0x7F` as `\x` and two
lowercase hexadecimal digits, such as `\x1b`. Every other byte is written as
it is, so UTF-8 text stays UTF-8. No other field holds a byte that needs
escaping.

**Examples.** In these lines `⇥` stands for a tab, and the line feed at the
end of each line is not shown:

```text
value⇥0⇥0⇥0⇥1/2
value⇥7⇥0⇥0⇥1 + 5*x + 10*x^2 + 10*x^3 + 5*x^4 + x^5
state⇥0⇥0⇥0⇥IterationLimit
error⇥0⇥0⇥0⇥Syntax⇥0..0⇥-⇥-⇥-⇥-⇥expected a number, an identifier, `-` or `(`
error⇥0⇥0⇥0⇥DivisionByZero⇥3..6⇥-⇥-⇥-⇥-⇥division by zero
error⇥3⇥2⇥1⇥ResourceLimit⇥2..5⇥Field(max_exponent)⇥-⇥256⇥Required(257)⇥resource limit exceeded: max_exponent
error⇥0⇥0⇥0⇥ResourceLimit⇥-⇥Field(max_nodes)⇥Value⇥12⇥Required(17)⇥resource limit exceeded: max_nodes
error⇥0⇥0⇥0⇥UnknownSymbol⇥-⇥-⇥-⇥-⇥-⇥eval needs a number, and the input holds a symbol, which has no value
error⇥0⇥0⇥0⇥Unsupported⇥-⇥-⇥-⇥-⇥-⇥unknown operation: the operations of this release are eval, expand and diff
```

They are the lines of `eval` of `1/3 + 1/6`; `expand` of `(x+1)^5` in `x`
with the input version 7; a state, which no operation of this release
reaches; `eval` of the empty input, whose operand is missing; `eval` of
`0*(1/0)`; `expand` of `x^257` under `max_exponent = 256`, with the input,
context and settings versions 3, 2 and 1; `expand` of `(x+1)^5` under
`max_nodes = 12`, whose power $(x + 1)^3$ needs 17 nodes; `eval` of `x`; and
the operation `simplify`, which this release does not have. The messages are
those of this release.

## The command-line program

The program `kalyx` runs requests of the command entry and writes the
[output line](#output-lines) of each to standard output, through
`kalyx::command::serialize` only. Its arguments and the fields of its
input lines are not part of the grammar of expressions: the program splits
them into the operation, the variable, the input and the limits of a
request, and the input is read by the grammar alone.

**Forms.** The arguments after the program name take one of these forms:

| Arguments | What the program does |
| --- | --- |
| none | Line mode: one request per line of standard input. |
| `--version` | Writes `kalyx` and the version of the package, such as `kalyx 0.1.0`, and a line feed. |
| `--help` or `-h` | Writes the usage text. |
| `[--limits LIMITS] OPERATION INPUT` | Argument mode: the request of `OPERATION` on `INPUT`, with the empty variable, which `eval` does not read. |
| `[--limits LIMITS] OPERATION VARIABLE INPUT` | Argument mode: the request of `OPERATION` on `INPUT` in `VARIABLE`, such as `expand x '(x+1)^2'`. |

`LIMITS` has the format of the `limits` column of the
[answer vectors](../vectors/README.md#format): `-` for the default limits,
or `field=value` settings separated by `;`, applied on top of the defaults,
where `field` is a field of `Limits` and `value` the decimal digits of a
`u64`, without a sign; no field may be set twice. The empty text is the
default limits as well. Options are read only before the operation: every
argument after it is an operand, so `kalyx eval -2` evaluates $-2$. The
operation is given to the command entry as it is: an operation that the
entry does not have, such as `simplify`, is a request that fails with
`Unsupported`, never a usage error and never another operation. Any other
form is a usage error: an operation without an input or with more than two
operands, an option other than these, `--limits` without its value or
without an operation, an invalid `LIMITS`, or an argument that is not
UTF-8.

**Line format.** In line mode the program reads standard input as lines,
each ended by a line feed; the last line may lack it. A line, without its
line feed and without one carriage return before it, holds up to four
fields separated by tabs:

```text
OPERATION⇥VARIABLE⇥INPUT⇥LIMITS
```

where `⇥` stands for a tab. The fields are the operation, the variable, the
input and the limits of the request, in the format of `LIMITS` above; a
field that the line does not have is empty, and empty limits are the
default limits. Since the tab separates fields, an input in line mode holds
no tab. A line with fewer fields is still a request: `eval` alone is the
request of `eval` with the empty input, which fails with `Syntax` at its
end, and the empty line is the request of the empty operation, which fails
with `Unsupported`. A line that is not UTF-8, has more than four fields or
has invalid limits is not a request: the program writes a diagnostic with
its line number to standard error, writes no line for it on standard
output, and goes on with the next line.

**Requests and lines.** For every request the program creates a context
with the limits of the request, a cancellation flag of its own, which
nothing in the program sets, and no deadline, runs `execute` under it, and builds the line of the outcome with
`serialize` under the same context. When that fails and the outcome is an
error, it builds the line again under a fresh context with the default
limits, a fresh flag and no deadline, the
[fallback step](components/command/contract.md#the-fallback-line) of the
command entry. A value or a state whose line fails under the context of its
request has no line: the program writes a diagnostic to standard error
instead. The line is complete before its first byte is written, and the
program writes it with one `write!` to the locked standard output and then
flushes it, so a cancellation or a limit leaves the whole line or nothing,
and a reader of line mode sees each line as soon as its request is done.
The versions of every request are 0. Line mode answers its lines in order,
one at a time; each request is independent of the others.

**Terminals.** When standard input is a terminal, line mode writes one
line of guidance to standard error before it reads; standard output is the
same either way.

**Exit statuses.**

| Status | Meaning |
| --- | --- |
| 0 | Every request gave a value or a state, or the version or the usage text was written. |
| 1 | Some request ended with an error, whose error line was written, or its value or state has no line under the limits of the request. |
| 2 | A usage error: the arguments are not one of the forms above, or a line of line mode is not a request. |
| 3 | Reading standard input or writing standard output failed, as when the reader of a pipe has closed it; the program stops at once. |

In line mode the status is the highest status of its lines. Diagnostics go
to standard error and start with `kalyx:`; a failure to write them is
ignored. The program never panics on input or on a closed stream: it
writes with `write!` and `flush` and returns its status from `main`.
