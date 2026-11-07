# Syntax

This contract states the parser of kalyx: how `parse` reads the text of an
expression in the one input grammar of the library into a term of the term
core; the three limits of the parser with their measures; its charges; the
spans of its errors; and its tests. It applies to the module `src/syntax.rs`
with its submodules in `src/syntax/`. The grammar itself, with its precedence
and associativity, its lexical rules, the reserved names, function-call
syntax and the mapping to the term core, is stated in
[the input syntax](../../semantics.md). The
[architecture](../../architecture.md#release-01) places the component among
the components of release 0.1, and the
[public API conventions](../../conventions/public-api.md) state the rules that
every public interface follows. The limits and the charges belong to the
[context](../context/contract.md), the errors to the
[errors and result states](../errors/contract.md), the decimal literals to the
[exact numbers](../numbers/contract.md) and the terms to the
[term core](../terms/contract.md).

**Status.** Implemented in `src/syntax.rs` and `src/syntax/`, at tier A1
(tested with a written contract). The parser is written anew for kalyx: no
code of the parser is taken over from the earlier implementation, which
served as a reference; cases of `tests/syntax.rs` are adapted from its parser
tests, as [PORTING](../../../PORTING.md) records. Its first caller in the
library is the [command entry](../command/contract.md), which gives it the
input of every request.

## Scope

- **Included.** The lexer, the parser and the private syntax tree, and the
  builder that turns the tree into a term; the three limits of the parser,
  the input bytes, the syntax depth and the syntax nodes; the charges of
  reading and building; the spans of every error; the faults of syntax, of
  function-call syntax and of the reserved names; and the reading of
  exponents as integers.
- **Excluded, with their owners.**
  - The canonical forms of terms, their display text and the checks of every
    node of a term: the [term core](../terms/contract.md).
  - The conversion of a decimal literal into a rational: the
    [exact numbers](../numbers/contract.md#decimal-literals), whose
    crate-internal `Rational::literal_at` the parser calls.
  - Command words, operations, settings and the serialization of outcomes:
    the [command entry](../command/contract.md), which gives the text of an
    operand to `parse`.
  - Each extension of the grammar, which comes with its first user: the
    syntax of the command line, with the command-line program later in
    release 0.1;
    function calls and the constants $\pi$, $i$ and `undefined`, release 0.2;
    set literals and program syntax, release 0.3; calls with several
    arguments, release 0.5; and the number literals `.5`, `1.` and
    scientific notation, release 0.7.

## Interface

The module `kalyx::syntax` holds one function:

```rust
pub fn parse(source: &str, context: &mut Context) -> Result<Term>
```

It has the shape of
[convention 5](../../conventions/public-api.md#5-uniform-parse-signature):
the source text first and the context last, and every error carries the byte
span of the text that caused it. The crate root re-exports it as
`kalyx::parse`, the one request-level reading function that
[convention 3](../../conventions/public-api.md#3-extensible-enums-and-records)
names. Nothing else of the component is public: the tokens, the syntax tree
and the stages are private, so the tree can change without changing the
interface.

Crate-internal items of other components that the parser uses:
`Rational::literal_at` and `Integer::magnitude_u64` of the exact numbers; the
rule of symbol names (`starts_name`, `continues_name`, `is_digit`,
`character_length`), `is_reserved` and `integer_exponent` of the term core;
`Error::with_default_span` of the errors; and `charge_at`, `check_at` and
`check_storage_at` of the context, which put the parser's span on their
errors.

## Rules

### Reading, then building

`parse` works in two stages:

1. **Reading.** The parser checks the length of the source, then reads its
   tokens one at a time, as it needs them, into a syntax tree. The tree is a
   vector of nodes in postorder: every node comes after the nodes of its
   operands, which it names by their indices, and the root is the last node.
   A number, an identifier, a unary minus and a power are one node each; a
   chain of `+` and `-`, or of `*` and `/`, is one node with its operands in
   order and the operator in front of each, where the operand after a `-` is
   a node of its negation and the operand after a `/` a node of its
   reciprocal, each right after the nodes of the operand; parentheses are no
   node, and only widen the range of the operand that they enclose. The parser does
   not evaluate anything, so every syntax error, every unsupported construct
   and every limit of the parser is reported before any term is built.
2. **Building.** The builder takes the nodes in order and builds the term of
   each through the constructors of the term core, as the
   [mapping](../../semantics.md#from-syntax-to-terms) states: the operands
   of a node are built before it, from left to right, and the first error
   ends the request. The operand behind a `-` is negated, and the operand
   behind a `/` raised to the power $-1$, as soon as it is built and before
   the next operand is, so the faults of strict evaluation come in the order
   of the left-associative reading of the chain; the chain itself is then
   built by one call of `Term::sum` or `Term::product`. The exponent of a
   power must be a number that is an integer, and is read as an `i64` by
   `integer_exponent`, the check of every exponent of the term core.

### Limits and their measures

The parser checks three limits, each through a field of `Limits` and the
checks of the [context](../context/contract.md), with no constant in their
place.

- **Input bytes.** Before any byte is read and before any charge, the length
  of the source in bytes is checked with `check(InputBytes, length)`. An
  excess fails with `LimitId::Field(InputBytes)`, the amount
  `LimitAmount::Required(length)`, no scope and the span of the whole source.
- **Syntax depth.** Every operand is read at a level. The whole input is at
  level 1, and one level deeper than the construct that holds them are: the
  contents of a pair of parentheses, the operand of a unary minus, the
  exponent of a power, and every operand of a chain after its first. The
  first operand of a chain and the base of a power are at the level of the
  chain or the power. The depth of an input is its greatest level. Before the
  parser reads an operand at a new level, it compares the level with
  `max_depth` through `check(Depth, level)`, and level 1 is checked before the
  first token; an excess fails with `LimitId::Field(Depth)`, the amount
  `Required(level)`, no scope, and the span of the token that opens the level:
  the `(`, the unary `-`, the `^` or the binary operator, and the whole
  source for level 1. So a chain of any length, such as `1+2+...+2048`, has
  the depth 2; a tower `2^3^4` has the depth 3; 127 nested parentheses around
  a number have the depth 128, and 128 fail under the default `max_depth` of
  128 at their 128th `(`. The depth cases of the answer vectors follow: 63
  sums right-nested in parentheses, `1+(1+(...(1)...))`, reach the depth 127
  and parse under the default limits; 64 of them fail at `max_depth` 32, at
  their 16th `(`, which opens the level 33; and 192 nested parentheses fail
  at `max_depth` 128, at their 128th `(`.
- **Syntax nodes.** The syntax nodes are the numbers, the identifiers, the
  unary minus signs, the powers and the binary operators `+`, `-`, `*` and
  `/` of the input; parentheses add none, so `((x))` has one node, `-x` two
  and `1+1+1+1` seven. When a node is complete, the count of the nodes so far,
  this one included, is checked with
  `check_storage(Storage::new(count, 0), LimitScope::Value)`: a syntax node
  costs one node and no logical bytes, as every count of elements of a
  temporary array is checked against `max_nodes`, and the bytes of the source
  are bounded by `max_input_bytes`. The open frames and the reserved
  temporaries count as well. An excess fails with `LimitId::Field(Nodes)`,
  the scope `Value` and the span of the node. The tree is not retained against
  the limits after the check; the terms that the builder makes are checked by
  the term core, node by node.

The term core checks the depth and the cost of every term that the builder
makes against the same `max_depth`, `max_nodes` and `max_storage_bytes`, with
its own measures. A term can be deeper than its syntax: `x/y + 1` has the
syntax depth 2, and its product $x y^{-1}$ the depth 3. Depth tests therefore
set `max_depth` to at least the depth that they test, as
[convention 15](../../conventions/public-api.md#15-depth) asks.

### Charges

Every step is charged to the context. The amounts depend only on the input,
never on the limits or the remaining work, so the same input charges the
same work under every limits that admit it.

| Step | Charge |
| --- | --- |
| The checks of the input bytes, of a level and of a node count | none |
| A token | 1 per byte from the end of the previous token to the end of this one, its leading whitespace included; the end of the input 1 more; charged after the token is scanned and before it is used |
| A number literal | as `Rational::literal_at`: the check of 4 bits per digit against `max_integer_bits`, then 1 per digit |
| A syntax node | 1, after its node check |
| Building a syntax node | 1, before the term core is called for it: a `-` or a `/` when its operand is negated or inverted, a `+` or a `*` when the chain takes its operand |
| The terms | the charges of the constructors of the term core |

So parsing a complete input charges its bytes and 1, the digits of its
literals, 2 per syntax node, and the work of the term core: `x` charges 6,
`12` charges 8 and `1.5` charges 9, and ` x + y ` charges 35: 8 for its 7
bytes and its end, 6 for its 3 syntax nodes, 4 for the two symbols and 17 for
their sum. A node that its node check rejects is not charged, so `x` under
`max_nodes` 0 charges 2, for its token and the end of the input; neither is a
character that starts no token, nor the whitespace before it. Every other
token is charged when it is read, before it is used, even when a check then
rejects it: the `(`, `-`, `^` or operator that opens a level beyond
`max_depth`, so `(1)` under `max_depth` 1 charges 1, and a literal that its
form or `max_integer_bits` rejects, which is not charged its digits. A
reserved name charges only its own token.

### Spans

Every error of `parse` carries a span: a half-open range of byte offsets into
the source, on character boundaries.

| Error | Span |
| --- | --- |
| The input is longer than `max_input_bytes` | the whole source |
| A character that starts no token | the whole character |
| A malformed number literal | its first character outside the form `1` or `1.5`, or an empty span at its end when a digit is missing after the point |
| A literal beyond `max_integer_bits` | the whole literal |
| A missing operand | the token found instead, or the empty span at the end of the input |
| An operand after an operand, without an operator | the first token of the second operand |
| A `)` without its `(` | the `)` |
| A `(` without its `)` | the empty span at the end of the input |
| A reserved name | the name |
| Function-call syntax | from the start of the name to the end of the `(` |
| A level beyond `max_depth` | the token that opens the level, or the whole source for level 1 |
| A syntax node beyond `max_nodes` | the node |
| A request failure of a charge | the token or the node that charged |
| An exponent that is not an integer, or beyond `max_exponent` | the exponent, with its parentheses |
| A negation of the operand of a subtraction, or the power $-1$ of a divisor, that fails | the operation: from the start of the chain to the end of that operand |
| Any other error of the term core | the node whose term failed |

The span of a node does not include the parentheses around it: a number or
an identifier is its token, a unary minus runs from its sign to the end of its
operand, a power from the start of its base to the end of its exponent, and a
chain from the start of its first operand to the end of its last. An operand
in parentheses includes them, so the division in `0*(1/0)` is at bytes 3 to
6, and the one in `(1)/0` at bytes 0 to 5. The errors of the term core carry
no span; the builder gives each of them the span of its node, through the
crate-internal `Error::with_default_span`, which keeps the span of an error
that already has one, such as the shifted span of an error of a literal.

### Errors

`parse` returns a term or one of these errors, and no other kind:

- `Fault(Syntax)` for input outside the grammar;
- `Fault(Unsupported)` for function-call syntax and the reserved names;
- `Fault(NonIntegerExponent)` for an exponent that is not an integer
  constant;
- `Fault(DivisionByZero)` for a division by zero and a negative power of zero
  or of a product with the coefficient 0, from the strict evaluation of the
  term core;
- `ResourceLimit` naming `max_input_bytes`, `max_depth` or `max_nodes` from
  the parser, `max_integer_bits` from a literal or the term core,
  `max_exponent` from an exponent or the term core, `max_nodes`,
  `max_storage_bytes` or `max_depth` from the term core, and `max_work`;
- `Cancelled` and `DeadlineExceeded`, the request failures of the charges;
- `Fault(Internal)`, only when an internal invariant is broken.

It never returns `Fault(UnknownSymbol)` or `Fault(NotPolynomial)`, which
belong to later stages of a request, and it never panics
([convention 12](../../conventions/public-api.md#12-no-panic)).

**Order of failures.** When an input breaks more than one rule, `parse`
reports the first failure in reading order. It checks the input bytes, then
level 1, then reads the tokens one at a time, each only when it needs it, and
checks a level or a syntax node at the step that opens the level or completes
the node, as [limits and their measures](#limits-and-their-measures) state;
every failure of reading comes before any term is built. Where two rules apply
to the same text, reading order decides:

- A reserved name fails as soon as it is read, before the token after it, so
  `pi(x)`, `pi (x)` and `pi$` fail with `Unsupported` and the span of the
  name.
- Any other identifier first reads the token after it, to detect
  function-call syntax, and only then is its node checked: `f(` fails with
  `Unsupported` whatever follows, and under `max_nodes` 0, `x$` fails with
  `Syntax` at the `$`, while `1$` fails with `max_nodes` at the `1`.
- A token that starts an operand right after a complete operand fails at
  once with `Syntax` and the span of that token, also when it is a reserved
  name, the name of function-call syntax or a malformed literal: `1 pi`,
  `1 f(x)` and `1 2x` fail at `pi`, `f` and `2x`.

### Traversal and stack

- **No native recursion.** The lexer reads one token per call with loops
  over the bytes; the parser is one loop over its steps, with the open
  constructs, parentheses, unary minus signs, powers and chains, on a stack
  on the heap whose frames hold copied scalars and the operand lists of
  chains, never borrowed references; and the builder is one loop over the
  nodes in postorder, with no stack at all, since the terms of the operands
  of a node are built before it. No function of the component calls itself,
  directly or through another.
- **Drop.** The syntax tree is a flat vector with indices, so dropping it
  does not recurse, and terms are dropped by the iterative drop of the term
  core.
- **Depth.** The native stack use of `parse` therefore does not grow with
  the nesting of the input: 20,000 nested parentheses parse on a stack of
  2 MiB, and so does an input that builds a term of depth 20,001. The stack
  of open constructs holds one frame for each level above level 1 of the
  operand being read, so at most `max_depth` frames. The tree has a node for
  each syntax node except the `+` and `*` of a chain, whose operands need no
  node of their own, and one more for each chain, so fewer than twice as many
  nodes as syntax nodes, which `max_nodes` bounds: `x-x` passes `max_nodes` 3
  with a tree of four nodes. Both grow at most linearly with the bytes of the
  input.

## Requirements

The earlier implementation has no requirement identifiers for its parser, so
the requirements of this component are named after what they state. Tests
are in `tests/syntax.rs` unless the entry names `src/syntax/tests.rs`,
`src/error.rs`, `src/term/exponent.rs` or `tests/syntax_properties.rs`.

### The single grammar

`parse` reads exactly the grammar of [the input syntax](../../semantics.md):
its productions, the precedence and associativity of its operators, unary
minus in front of every operand and after `^`, and its whitespace.

- **Implemented here.** `src/syntax/lexer.rs` and `src/syntax/parser.rs`.
- **Evidence.** `the_first_five_eval_vectors_parse_to_their_answers`,
  `every_evaluation_of_r02_is_decided_by_the_parser`,
  `precedence_and_associativity_follow_the_grammar`,
  `a_unary_minus_may_start_every_operand`, `whitespace_separates_tokens`
  and, in `src/syntax/tests.rs`,
  `tokens_cover_the_input_and_charge_its_bytes` and
  `the_tree_is_in_postorder_with_the_root_last`.

### Number literals

A number literal is the whole run of letters, digits, `_` and points that
starts with a digit or a point, converted exactly by the decimal literal
function of the exact numbers; only the forms `1` and `1.5` are valid, so
`.5`, `1.` and `1e-3` fail with `Syntax` and a span.

- **Implemented here.** The literal run of `src/syntax/lexer.rs`, and the call
  of `Rational::literal_at` in `src/syntax/parser.rs`.
- **Evidence.** `decimal_literals_are_read_by_the_literal_function` and
  `incomplete_and_scientific_literals_are_syntax_errors`.

### Limits of the parser

The input bytes, the syntax depth and the syntax nodes are checked as
[limits and their measures](#limits-and-their-measures) state, each failing
with `ResourceLimit`, its own field and a span.

- **Implemented here.** `read`, `deeper` and `SyntaxParser::complete` in
  `src/syntax/parser.rs`.
- **Evidence.** `input_bytes_are_checked_before_any_byte_is_read`,
  `syntax_nodes_are_checked_against_max_nodes`,
  `the_syntax_depth_is_checked_against_max_depth` and
  `the_depth_vectors_of_r02`.

### Deep input on a small stack

Input of any nesting that the limits admit is read and built with a native
stack that does not grow with its nesting.

- **Implemented here.** The loops of `src/syntax/parser.rs` and
  `src/syntax/build.rs`.
- **Evidence.** `twenty_thousand_nested_parentheses_on_a_2_mib_stack`, with
  `max_depth` raised above the tested depth for the result and the default
  limits for the failure, unary minus signs nested as deeply, and
  10,000 products nested in sums, `x*(y+x*(y+...x...))`, which the builder
  turns into a term of depth 20,001 on the same stack.

### Function calls, reserved names and command words

Function-call syntax and the reserved names `pi`, `i` and `undefined` fail
with `Unsupported` where an operand is expected, and right after a complete
operand with `Syntax`, as the [order of failures](#errors) states; command
words are not part of the grammar.

- **Implemented here.** `identifier` in `src/syntax/parser.rs`, with
  `is_reserved` of the term core.
- **Evidence.** `function_call_syntax_is_unsupported`,
  `reserved_names_are_unsupported`, `command_words_are_ordinary_names` and
  `failures_come_in_reading_order`.

### Terms through the term core

The term of an input is built through the constructors of the term core as
the [mapping](../../semantics.md#from-syntax-to-terms) states, operands
before operations, from left to right; exponents are integer constants; and
numbers are evaluated strictly.

- **Implemented here.** `src/syntax/build.rs`, with `integer_exponent` of the
  term core.
- **Evidence.** `exponents_are_integer_constants`,
  `numbers_are_evaluated_strictly`, `the_error_vectors_of_r02`,
  `every_evaluation_of_r02_is_decided_by_the_parser` and, in
  `src/term/exponent.rs`, `integers_become_exponents_under_the_same_check`.

### Spans

Every error carries the span that [spans](#spans) states.

- **Implemented here.** The ranges of the tokens and nodes of
  `src/syntax/tree.rs`, and `spanned` in `src/syntax/build.rs`.
- **Evidence.** `syntax_errors_carry_the_span_of_their_text`,
  `errors_of_the_term_core_carry_the_span_of_their_node`,
  `request_failures_carry_the_span_of_their_step`, and, in
  `src/syntax/tests.rs`, `chains_keep_the_ranges_of_their_operations` and
  `powers_and_negations_keep_their_ranges`; and, in `src/error.rs`,
  `a_default_span_fills_only_a_missing_span`.

### Order of failures

An input that breaks more than one rule fails with the first failure in
reading order, as the [errors](#errors) state.

- **Implemented here.** The loop of `src/syntax/parser.rs`, which reads a
  token only when it needs it, and `identifier`, which rejects a reserved
  name before it reads the token after it.
- **Evidence.** `failures_come_in_reading_order`, and the reading of
  reserved names and calls by the model of
  `full_inputs_give_only_the_listed_errors_with_spans_in_the_input` in
  `tests/syntax_properties.rs`.

### Display text reads back

The display text of every term of this release parses into the same term
under limits that admit the text.

- **Implemented here.** The grammar, whose productions cover every form of
  the display grammar of the term core except the reserved call.
- **Evidence.** `the_display_of_a_term_reads_back`, and the round trip of
  [testing obligation 8](#testing-obligations) in
  `tests/syntax_properties.rs`.

### Accounting under the request context

Every step is charged as [charges](#charges) state, and the charges do not
depend on the limits.

- **Implemented here.** `next_token` in `src/syntax/lexer.rs`,
  `SyntaxParser::complete` in `src/syntax/parser.rs` and the charges of
  `src/syntax/build.rs`.
- **Evidence.** `charges_follow_the_charge_table`, the charge of a rejected
  node in `syntax_nodes_are_checked_against_max_nodes`, and
  `tokens_cover_the_input_and_charge_its_bytes` in `src/syntax/tests.rs`.

### Arbitrary input

Every input gives a term or an error of the kinds that [errors](#errors)
list, and never a panic.

- **Implemented here.** The whole component.
- **Evidence.** The random inputs of
  [testing obligation 8](#testing-obligations) in
  `tests/syntax_properties.rs`.

## Testing obligations

1. **Grammar.** The first five cases of the answer vectors, the evaluations,
   parse to their answers, among them `-2^2 + 2^3^2` to 508, and every other
   evaluation of the answer vectors parses to its answer or fails with the
   kind of its result; each precedence level, each associativity and each
   place of a unary minus has a case.
2. **Literals.** `1.5` is $3/2$ through the decimal literal function, and
   `.5`, `1.` and `1e-3` each fail with `Syntax` and a span.
3. **Limits.** One negative case each for `max_input_bytes`, the syntax nodes
   and `max_depth`, each a `ResourceLimit` with its `LimitId` and a span; the
   three depth cases of the answer vectors, and their limits of integer bits
   and of an exponent, under their limits.
4. **Depth.** 20,000 nested parentheses on a thread with a stack of 2 MiB give
   a result with `max_depth` raised, and `ResourceLimit` under the default
   limits, and an input whose term has the depth 20,001 is built on the same
   stack; none overflows the stack.
5. **Calls, reserved names, command words.** Function-call syntax fails with
   `Unsupported` and its span, as each reserved name does, and command words
   are identifiers.
6. **Spans.** Typical syntax errors, the errors of the term core and the
   request failures carry the spans of this contract, and the examples of the
   order of failures fail in reading order.
7. **Work.** Tests pin the charges of a few inputs and check that the charges
   do not depend on the limits; they assert no other amount.
8. **Random input and round trips.** Property tests from fixed seeds in
   `tests/syntax_properties.rs`, written by an author other than the author of
   the parser:
   - 10,000 inputs over an alphabet without `/`, `^` and letters: digits,
     `.`, `+`, `-`, `*`, parentheses, spaces and some characters outside the
     syntax, among them characters outside ASCII; each gives a term, a
     `Syntax` error or a `ResourceLimit`, and none panics;
   - 10,000 inputs over the full alphabet of the grammar with the same extra
     characters; none panics, and each gives a term or an error of a kind
     that [errors](#errors) list;
   - 1,000 round trips: a random term built through the constructors of the
     term core, displayed and parsed back, equals the term (`Term::equals`).
9. **No message text.** No test asserts the message of an error; tests
   compare the kind, the span and the exceeded limit.

## Extractability

The parser is at tier A1, and no proof is planned for it. It is written in
the style of the provable subset of Rust that the term core follows, the krepi
convention on the provable subset, so that it can join a proof target without
a rewrite; none of its code has been extracted.

- **Constructs.** No function item is passed as a value (R1), no
  `Iterator::any` (R2) or `Iterator::flatten` (R3) is called, and no closure is
  given to a combinator, an adapter or a parameter (R4): `match` takes the
  place of combinators, and scans are loops over bytes. No mutable borrow of an
  element is held across a write to another value (R5). The enumerations
  have names that are unique in kalyx: `SyntaxTokenKind`, `SyntaxOperator`,
  `SyntaxShape`, `SyntaxChainKind`, `SyntaxFrame` and `SyntaxStep` (R6). R7
  concerns Lean code, which the component does not have.
- **Loop shapes.** A function has at most one loop, at the top level of its
  body, and no function with a loop leaves before it; byte slices and operand
  lists are walked by index loops, the nodes by `while let` over `Vec::pop`,
  and the steps of the parser by `while let` over a step function called with
  `?`; no loop condition is a macro.
- **Frames and state.** The frames of the parser hold copied scalars and the
  owned operand lists of chains; no frame and no structure has a lifetime
  parameter, since the source is passed to each function that reads it.
- **Integer conversions.** `usize` to `u64` is an `as` cast, which loses
  nothing on the 64-bit targets that the library supports; an exponent
  becomes an `i64` by an `as` cast of its magnitude after the bound check of
  `integer_exponent`, and that magnitude comes from `Integer::magnitude_u64`
  of the exact numbers. No `try_from`, `unsigned_abs` or `From` conversion
  between machine integers is used.
- **Design rules.** The check of the input bytes comes before any charge, and
  the check of a node count before the charge and the write of its node; a
  level is checked after the charge of the token that opens it, which belongs
  to the step of that token, and before its frame is pushed; and a literal is
  charged as a token before `literal_at` checks it (1). The tree, the operand
  lists of chains, the stack of frames and the builder's list of terms are
  allocated at run time, bounded by the bytes of the input, by twice
  `max_nodes` and by `max_depth`; tokens are copied values and are never
  stored; rules 2 and 3 are written for kernels and do not apply. Every loop
  is bounded by charged steps: a scan over whitespace, a literal or an
  identifier is followed by the charge of every byte that it read, unless it
  ends at a character that starts no token, which ends the request; every
  step of the parser reads a charged token, completes a charged syntax node,
  or applies a token that an earlier step read to the frame on top of the
  stack, pushing the frame that the token opens or popping the group that a
  `)` closes; and the builder charges every syntax node, so that only the
  first operand of a chain is taken without a charge (4). The level of an
  operand, the count of syntax nodes and the range of a node are fields
  (5). Every syntax type is private to the component, so no compile-time
  guard is needed (6). There is no `Cell`, no `RefCell` and no `cfg` other
  than the test module (7, 8), and the library forbids `unsafe` code (9).
- **External declarations.** No code has been extracted, so this list
  follows the records that the [term core](../terms/contract.md#extractability)
  cites. Recorded as external: `Vec::pop`, `str::len` and `str::as_bytes`.
  Recorded as translated with library models: `Vec::push`, slice indexing and
  `len` of `Vec` and slices. Not recorded: `Vec::new`, `Vec::with_capacity`,
  `Vec::reverse`, the `vec!` macro, `slice::get`, `slice::get_mut`, `str::get`
  with a range, `Option::take`, `Option::is_none` in
  `Error::with_default_span`, and `saturating_add` and `saturating_sub` on
  `usize` and `u64`. An extraction also needs the operations of `Rational`
  and `Integer` that the parser calls, `is_integer` and `numerator`, besides
  `Rational::literal_at`, which scans with `str::char_indices`, and
  `Integer::magnitude_u64`, which uses `ToPrimitive::to_u64`, both outside the
  subset; the context methods `check_at`, `check_storage_at`, `charge_at`
  and, through `integer_exponent`, `check_width_at`, with `Storage::new`; the
  constructors of the term core with `Term::as_number`, and the shared
  helpers `integer_exponent`, `is_reserved`, `starts_name`, `continues_name`,
  `is_digit` and `character_length`; `Span::new`; and `Error::new`, whose
  string literals each add a `decide +native` axiom.

## Current deviations

None: the code and the tests follow every rule above.
