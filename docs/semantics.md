# Input syntax and semantics

This document states the one grammar of the input of kalyx, the text of an
expression that a request gives to the library, and how that text becomes a
term of the [term core](components/terms/contract.md). The parser,
`kalyx::syntax::parse` (also `kalyx::parse`), reads it. Its
[contract](components/syntax/contract.md) states the limits of the parser
with their measures, its charges, its spans and errors, and its tests.

**Status.** The grammar of this release reads numbers, identifiers, the binary
operators `+`, `-`, `*`, `/` and `^`, parentheses and unary minus, and is
implemented in `src/syntax.rs` and `src/syntax/`. Later releases extend it as
[the single-grammar rule](#the-single-grammar-rule) states.

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
  evaluation, expansion and differentiation are chosen by the command entry,
  which is planned for this release, before it gives the text of an operand
  to `parse`. Inside an expression, a word such as `eval`, `expand` or `diff`
  is an ordinary identifier, so `diff` is the symbol named `diff`, and
  `diff(x)` is function-call syntax.
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
