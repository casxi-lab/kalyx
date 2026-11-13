//! The slice replay of the full vectors in `vectors/`, the outcomes of the
//! earlier implementation.
//!
//! A slice is the part of the full vectors that one capability answers. The
//! table `SLICES` names each slice by the commands of its command-line cases
//! (the `command` column of `cli_cases.tsv`), the requests of its root calls
//! (the `request` column of `root_calls.tsv`) and the operations of its
//! library observations (the `operation` column of `library.tsv`, with the
//! inputs that the slice takes of them), and states the rows that it selects
//! in each file. Three kinds of rows belong to no slice: the sessions, which
//! are the cases of the line mode `repl` and the two terminal sessions; the
//! integration tests, which are a list and not answers; and the rows of the
//! commands, requests and inputs that no slice names. They are neither
//! replayed nor counted as pending, and a test checks how many there are.
//!
//! A slice is enabled when the dispatch table of the command entry registers
//! every command that it names, and pending otherwise. The replay reads the
//! three files once and replays the rows of an enabled slice, each row that
//! it runs as one request through `execute`. It compares only the answer,
//! read with `parse` and compared by canonical form, the result state and
//! the error kind, never display text or work, and reports a row that no
//! request can express yet as a difference. A scope, a ring and the
//! operands of a command become entries of the operand table of the
//! request, and a condition and a scope of an answer are split from its
//! text. The rows of the pending slices are counted. `vectors/README.md`
//! states how a row becomes a request and under which limits it runs.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap the rows that tests/vectors.rs checks, and the tests panic with the differences that they find"
)]

#[allow(
    dead_code,
    reason = "the module also serves tests/vectors.rs, which checks all six files; the replay reads three of them"
)]
mod full_vectors;

use std::collections::BTreeSet;
use std::sync::OnceLock;

use full_vectors::{CLI_CASES, File, LIBRARY, ROOT_CALLS};
use kalyx::command::Answer;
use kalyx::context::CancelFlag;
use kalyx::{
    Context, ErrorKind, FaultKind, LimitExceeded, LimitField, LimitId, Limits, MathState, Outcome,
    Request, Settled, execute, parse,
};

// ---------------------------------------------------------------------------
// The slices

/// A library operation of a slice.
struct Operation {
    /// The `operation` column of `library.tsv`.
    name: &'static str,
    /// The kalyx command of the operation, by the table of the library
    /// observations in `vectors/README.md`.
    command: &'static str,
    /// The operands of the command beyond its variable and input, by the
    /// same table, each as its role and text: entries of the operand table
    /// of the request.
    operands: &'static [(&'static str, &'static str)],
    /// The inputs that the slice takes, or none for every input.
    inputs: &'static [&'static str],
    /// Whether the command answers every scope with the same request. A
    /// scope assumes a property of `x`; the polynomial expansion takes no
    /// scope, since an assumption on `x` does not change a polynomial. The
    /// rows of every other operation in a scope other than `none` give the
    /// request the entry of the role `scope`.
    scope_free: bool,
}

/// A slice of the full vectors.
struct Slice {
    /// The name of the capability.
    name: &'static str,
    /// The commands of its command-line cases, which the dispatch table must
    /// register for the slice to be enabled.
    commands: &'static [&'static str],
    /// The requests of its root calls.
    requests: &'static [&'static str],
    /// The operations of its library observations.
    operations: &'static [Operation],
    /// The rows that it selects in `cli_cases.tsv`, `library.tsv` and
    /// `root_calls.tsv`.
    rows: [usize; 3],
}

/// The eight inputs of `library.tsv` that denote a polynomial in
/// $\mathbb{Q}[x]$ in the syntax of release 0.1.
const POLYNOMIAL_INPUTS: [&str; 8] = ["(-x)^2", "(x+x)^3", "-x", "-x^3", "0", "0^0", "x", "x+x-x"];

/// The slices: first the two of the commands of release 0.1, then the
/// pending slices, which name commands that kalyx does not have yet.
static SLICES: [Slice; 15] = [
    Slice {
        name: "exact_numbers",
        commands: &["eval"],
        requests: &[],
        operations: &[],
        rows: [9, 0, 0],
    },
    Slice {
        name: "polynomials",
        commands: &["expand", "diff"],
        requests: &[],
        operations: &[Operation {
            name: "expand",
            command: "expand",
            operands: &[],
            inputs: &POLYNOMIAL_INPUTS,
            scope_free: true,
        }],
        rows: [5, 256, 0],
    },
    Slice {
        name: "function_expressions",
        commands: &["fexpr", "simplify"],
        requests: &["parse"],
        operations: &[
            Operation {
                name: "parse",
                command: "fexpr",
                operands: &[],
                inputs: &[],
                scope_free: false,
            },
            Operation {
                name: "simplify",
                command: "simplify",
                operands: &[],
                inputs: &[],
                scope_free: false,
            },
        ],
        rows: [7, 3_645, 162],
    },
    Slice {
        name: "questions_and_refinement",
        commands: &["f-refine", "ask", "f-ask"],
        requests: &["refine positive", "ask real"],
        operations: &[Operation {
            name: "ask",
            command: "f-ask",
            operands: &[("property", "positive")],
            inputs: &[],
            scope_free: false,
        }],
        rows: [3, 2_976, 324],
    },
    Slice {
        name: "substitution",
        commands: &["f-subs", "subs", "at"],
        requests: &["substitute -8"],
        operations: &[],
        rows: [20, 0, 162],
    },
    Slice {
        name: "function_derivatives",
        commands: &["f-diff", "rat-diff"],
        requests: &["differentiate"],
        operations: &[Operation {
            name: "diff",
            command: "f-diff",
            operands: &[("order", "1")],
            inputs: &[],
            scope_free: false,
        }],
        rows: [6, 2_976, 162],
    },
    Slice {
        name: "series",
        commands: &["f-series"],
        requests: &["series"],
        operations: &[],
        rows: [2, 0, 162],
    },
    Slice {
        name: "univariate_polynomials",
        commands: &[
            "compose",
            "discriminant",
            "divrem",
            "gcd",
            "gcdex",
            "resultant",
            "squarefree",
        ],
        requests: &[],
        operations: &[],
        rows: [16, 0, 0],
    },
    Slice {
        name: "univariate_factorization",
        commands: &["factor", "apart"],
        requests: &[],
        operations: &[],
        rows: [7, 0, 0],
    },
    Slice {
        name: "multivariate_polynomials",
        commands: &[
            "mdiff",
            "mdiv",
            "mfactor",
            "mgcd",
            "mp-at",
            "mpoly",
            "msubs",
            "poly-ring",
        ],
        requests: &[],
        operations: &[],
        rows: [17, 0, 0],
    },
    Slice {
        name: "real_roots",
        commands: &["roots", "count-roots", "refine"],
        requests: &[],
        operations: &[],
        rows: [12, 0, 0],
    },
    Slice {
        name: "real_algebraic_numbers",
        commands: &[
            "alg",
            "alg-root",
            "radical",
            "alg-compare",
            "minpoly",
            "alg-at",
        ],
        requests: &[],
        operations: &[],
        rows: [12, 0, 0],
    },
    Slice {
        name: "complex_algebraic_numbers",
        commands: &[
            "complex",
            "complex-at",
            "complex-equal",
            "complex-imag",
            "complex-minpoly",
            "complex-real",
            "complex-root",
            "complex-roots",
            "conjugate",
            "norm2",
            "principal-root",
        ],
        requests: &[],
        operations: &[],
        rows: [19, 0, 0],
    },
    Slice {
        name: "number_fields",
        commands: &["field-element", "field-value", "number-field"],
        requests: &[],
        operations: &[],
        rows: [6, 0, 0],
    },
    Slice {
        name: "real_sets_and_inequalities",
        commands: &[
            "contains",
            "ineq",
            "interval",
            "rel-and",
            "rel-not",
            "rel-or",
            "set",
            "set-complement",
            "set-difference",
            "set-intersect",
            "set-union",
        ],
        requests: &[],
        operations: &[],
        rows: [19, 0, 0],
    },
];

/// The slice named `name`.
fn slice(name: &str) -> &'static Slice {
    SLICES
        .iter()
        .find(|slice| slice.name == name)
        .unwrap_or_else(|| panic!("no slice {name}"))
}

/// Whether the dispatch table of the command entry registers `command`. The
/// entry fails a request whose operation the table does not hold with
/// `Unsupported`, without a span and before any work, and charges work for
/// every operation that it holds before that operation can fail on the
/// input `x`.
fn registered(command: &str) -> bool {
    let mut context = Context::new(Limits::new(), CancelFlag::new());
    let outcome = execute(&Request::new(command, "x", "x"), &mut context);
    let unknown = matches!(
        outcome.result(),
        Err(error) if error.kind() == ErrorKind::Fault(FaultKind::Unsupported)
            && error.span().is_none()
    );
    !(unknown && context.work_used() == 0)
}

/// Whether every command of `slice` is registered.
fn enabled(slice: &Slice) -> bool {
    slice.commands.iter().all(|command| registered(command))
}

// ---------------------------------------------------------------------------
// The rows

/// One row of a file of the full vectors, with its fields decoded.
struct Row {
    /// The columns of the file.
    columns: &'static [&'static str],
    /// The values of the fields, `None` for `-`.
    fields: Vec<Option<String>>,
}

impl Row {
    /// The value of `column`, `None` for `-`.
    fn get(&self, column: &str) -> Option<&str> {
        let index = self
            .columns
            .iter()
            .position(|known| *known == column)
            .unwrap_or_else(|| panic!("no column {column}"));
        self.fields[index].as_deref()
    }

    /// The value of `column`, which the row has.
    fn text(&self, column: &str) -> &str {
        self.get(column)
            .unwrap_or_else(|| panic!("no value in the column {column}"))
    }
}

/// The rows of `file`, read from `bytes`.
fn read(file: &File, bytes: &[u8]) -> Vec<Row> {
    let lines = full_vectors::lines(bytes).unwrap();
    let (header, rows) = lines.split_first().unwrap();
    assert_eq!(header.as_slice(), file.columns, "{}", file.name);
    rows.iter()
        .map(|fields| Row {
            columns: file.columns,
            fields: fields
                .iter()
                .map(|field| full_vectors::decode(field).unwrap())
                .collect(),
        })
        .collect()
}

/// The rows of the three files that the slices select from.
struct Vectors {
    cli: Vec<Row>,
    library: Vec<Row>,
    root_calls: Vec<Row>,
}

impl Vectors {
    /// The rows of the three files, read from their bytes.
    fn read(cli: &[u8], library: &[u8], root_calls: &[u8]) -> Self {
        Self {
            cli: read(&CLI_CASES, cli),
            library: read(&LIBRARY, library),
            root_calls: read(&ROOT_CALLS, root_calls),
        }
    }
}

/// The full vectors, read once for all the tests of this file.
fn vectors() -> &'static Vectors {
    static VECTORS: OnceLock<Vectors> = OnceLock::new();
    VECTORS.get_or_init(|| Vectors::read(CLI_CASES.bytes, LIBRARY.bytes, ROOT_CALLS.bytes))
}

/// The rows that a slice selects.
struct Selection<'v> {
    cli: Vec<&'v Row>,
    library: Vec<(&'static Operation, &'v Row)>,
    root_calls: Vec<&'v Row>,
}

impl Selection<'_> {
    /// The numbers of the selected rows, by file.
    fn rows(&self) -> [usize; 3] {
        [self.cli.len(), self.library.len(), self.root_calls.len()]
    }
}

/// The rows of `vectors` that `slice` selects: the command-line cases of its
/// commands, the library observations of its operations and inputs, and the
/// root calls of its requests.
fn select<'v>(slice: &'static Slice, vectors: &'v Vectors) -> Selection<'v> {
    let cli = vectors
        .cli
        .iter()
        .filter(|row| {
            row.get("command")
                .is_some_and(|command| slice.commands.contains(&command))
        })
        .collect();
    let library = vectors
        .library
        .iter()
        .filter_map(|row| {
            let (name, input) = (row.text("operation"), row.text("input"));
            slice
                .operations
                .iter()
                .find(|operation| {
                    operation.name == name
                        && (operation.inputs.is_empty() || operation.inputs.contains(&input))
                })
                .map(|operation| (operation, row))
        })
        .collect();
    let root_calls = vectors
        .root_calls
        .iter()
        .filter(|row| slice.requests.contains(&row.text("request")))
        .collect();
    Selection {
        cli,
        library,
        root_calls,
    }
}

// ---------------------------------------------------------------------------
// The replay

/// The full budget of a library observation, above the work of every
/// request of the file in the earlier work units.
const FULL_BUDGET: u64 = 1_000_000;

/// What the replay of one row did.
enum Disposition {
    /// The row ran as a request; `Err` says how its outcome differs from
    /// the expectation of the row.
    Compared(Result<(), String>),
    /// A usage error of the command-line program, exit status 2, which the
    /// library entry does not have: not compared.
    Usage,
    /// A budget in the earlier work units other than 0 and the full budget,
    /// whose outcome depends on how work is counted: not compared.
    Budget,
}

/// What the replay of the rows of one slice found.
#[derive(Debug, Default)]
struct Replay {
    /// The rows that ran and were compared.
    compared: usize,
    /// The usage errors, not compared.
    usage: usize,
    /// The rows under a budget that depends on how work is counted, not
    /// compared.
    budget: usize,
    /// One line for each row whose outcome differs: the file, the id, what
    /// the row expects and what kalyx gave.
    differences: Vec<String>,
}

impl Replay {
    fn add(&mut self, file: &File, row: &Row, disposition: Disposition) {
        match disposition {
            Disposition::Compared(result) => {
                self.compared += 1;
                if let Err(difference) = result {
                    let id = row.text("id");
                    self.differences
                        .push(format!("{} {id}: {difference}", file.name));
                }
            }
            Disposition::Usage => self.usage += 1,
            Disposition::Budget => self.budget += 1,
        }
    }
}

/// Replays every row of `selection`.
fn replay(selection: &Selection<'_>) -> Replay {
    let mut replay = Replay::default();
    for row in &selection.cli {
        replay.add(&CLI_CASES, row, cli_case(row));
    }
    for (operation, row) in &selection.library {
        replay.add(&LIBRARY, row, observation(operation, row));
    }
    for row in &selection.root_calls {
        replay.add(&ROOT_CALLS, row, root_call(row));
    }
    replay
}

/// The outcome of `request` under `limits`, in a context whose flag is
/// cancelled before the request when `cancelled` holds.
fn run(request: &Request, limits: Limits, cancelled: bool) -> Outcome {
    let flag = CancelFlag::new();
    if cancelled {
        flag.cancel();
    }
    let mut context = Context::new(limits, flag);
    execute(request, &mut context)
}

/// The request of a command-line case, with the limits that it runs under
/// and the field that a `ResourceLimit` must name, or how the case is
/// replayed without a request. Its arguments are the input, `--var NAME`,
/// the variable, `x` when it is not given, and `--work N`, the budget; the
/// case runs under the default limits, with `max_work=0` for `--work 0`. A
/// scope argument such as `{x:positive}` becomes the entry of the role
/// `scope`, and a ring argument such as `Q[x,y]:lex` the entries of the
/// roles `variables` and `monomial_order`; after them a request takes one
/// argument, its input.
fn cli_request(row: &Row) -> Result<(Request, Limits, Option<LimitField>), Disposition> {
    if row.text("kind") == "usage" {
        return Err(Disposition::Usage);
    }
    let args: Vec<&str> = row
        .get("args")
        .map_or_else(Vec::new, |args| args.split('\t').collect());
    let mut variable = "x";
    let mut budget = None;
    let mut operands = Vec::new();
    let mut entries: Vec<(&str, String)> = Vec::new();
    let mut items = args.iter();
    while let Some(&item) = items.next() {
        match item {
            "--var" => match items.next() {
                Some(&name) => variable = name,
                None => {
                    return Err(Disposition::Compared(Err(
                        "`--var` without a name".to_owned()
                    )));
                }
            },
            "--work" => match items.next().and_then(|n| n.parse::<u64>().ok()) {
                Some(n) => budget = Some(n),
                None => {
                    return Err(Disposition::Compared(Err(
                        "`--work` without a budget".to_owned()
                    )));
                }
            },
            operand => {
                if let Some(scope) = scope_argument(operand) {
                    entries.extend(scope.map(|text| ("scope", text)));
                } else if let Some((variables, order)) = ring_argument(operand) {
                    entries.push(("variables", variables));
                    entries.push(("monomial_order", order));
                } else {
                    operands.push(operand);
                }
            }
        }
    }
    if budget.is_some_and(|n| n != 0) {
        return Err(Disposition::Budget);
    }
    let [input] = operands.as_slice() else {
        return Err(Disposition::Compared(Err(format!(
            "{} operands, where a request has one input",
            operands.len()
        ))));
    };
    let (limits, field) = if budget == Some(0) {
        (Limits::new().with_max_work(0), Some(LimitField::Work))
    } else {
        (Limits::new(), None)
    };
    let mut request = Request::new(row.text("command"), variable, input);
    for (role, text) in &entries {
        request = request.with_operand(role, text);
    }
    Ok((request, limits, field))
}

/// The scope of a scope argument of the earlier command-line program, such
/// as `{x:positive}` or `{x:real,y:positive}`, as the text of the role
/// `scope`, `x: positive, y: real` with a space after each `:` and `,`;
/// `Some(None)` for the empty scope `{}`, which holds no facts and so gives
/// no entry, as the default of the role; and `None` for an argument that is
/// no scope, such as a program `{ 1 }`.
fn scope_argument(item: &str) -> Option<Option<String>> {
    let inner = item.strip_prefix('{')?.strip_suffix('}')?;
    if inner.is_empty() {
        return Some(None);
    }
    let mut facts = Vec::new();
    for fact in inner.split(',') {
        let (name, property) = fact.trim().split_once(':')?;
        let (name, property) = (name.trim(), property.trim());
        if !is_name(name) || !is_name(property) {
            return None;
        }
        facts.push(format!("{name}: {property}"));
    }
    Some(Some(facts.join(", ")))
}

/// The variables and the monomial order of a ring argument of the earlier
/// command-line program, `Q[x,y]:lex`, as the texts of the roles `variables`,
/// `x, y` with a space after each `,`, and `monomial_order`, `lex`; the
/// ring without variables `Q[]:lex` has the empty text of `variables`.
/// `None` for an argument that is no ring.
fn ring_argument(item: &str) -> Option<(String, String)> {
    let (variables, order) = item.strip_prefix("Q[")?.split_once("]:")?;
    let names: Vec<&str> = if variables.is_empty() {
        Vec::new()
    } else {
        variables.split(',').map(str::trim).collect()
    };
    if !names.iter().all(|name| is_name(name)) || !is_name(order) {
        return None;
    }
    Some((names.join(", "), order.to_owned()))
}

/// Whether `text` is an identifier: an ASCII letter or `_`, then ASCII
/// letters, digits and `_`.
fn is_name(text: &str) -> bool {
    let mut bytes = text.bytes();
    bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

/// Replays a command-line case as its request; its expectation is its
/// `kind` and, for `ok`, its standard output without the final line feed.
fn cli_case(row: &Row) -> Disposition {
    let (request, limits, field) = match cli_request(row) {
        Ok(request) => request,
        Err(disposition) => return disposition,
    };
    let outcome = run(&request, limits, false);
    let answer = row
        .get("stdout")
        .map(|stdout| stdout.strip_suffix('\n').unwrap_or(stdout));
    Disposition::Compared(compare(row.text("kind"), answer, field, &outcome))
}

/// The text of the role `scope` for a scope of the `scope` column of the
/// library observations: `none` gives no entry, and `real`, `pos` and `neg`
/// assume that `x` is real, positive or negative.
fn scope_entry(scope: &str) -> Option<&'static str> {
    match scope {
        "none" => None,
        "real" => Some("x: real"),
        "pos" => Some("x: positive"),
        "neg" => Some("x: negative"),
        other => panic!("no scope {other}"),
    }
}

/// The request of a library observation: the command of `operation` on the
/// input of `row`, in the variable `x`, with the entry of the role `scope`
/// for a scope other than `none` when the command reads a scope, then an
/// entry for each operand of the command.
fn observation_request(operation: &Operation, row: &Row) -> Request {
    let mut request = Request::new(operation.command, "x", row.text("input"));
    if !operation.scope_free
        && let Some(scope) = scope_entry(row.text("scope"))
    {
        request = request.with_operand("scope", scope);
    }
    for (role, text) in operation.operands {
        request = request.with_operand(role, text);
    }
    request
}

/// Replays a library observation as the request of the command of
/// `operation` on its input: with the full budget under the default
/// limits; with the budget 0 under `max_work=0`; cancelled under the
/// default limits, with the flag cancelled before the request.
fn observation(operation: &Operation, row: &Row) -> Disposition {
    let budget: u64 = row
        .text("limits")
        .strip_prefix("max_work=")
        .and_then(|budget| budget.parse().ok())
        .expect("the limits of an observation are max_work=<budget>");
    let cancelled = row.text("cancelled") == "yes";
    let (limits, field) = match (cancelled, budget) {
        (true, _) | (false, FULL_BUDGET) => (Limits::new(), None),
        (false, 0) => (Limits::new().with_max_work(0), Some(LimitField::Work)),
        (false, _) => return Disposition::Budget,
    };
    let request = observation_request(operation, row);
    let outcome = run(&request, limits, cancelled);
    Disposition::Compared(compare(
        row.text("result"),
        row.get("answer"),
        field,
        &outcome,
    ))
}

/// Replays a root call: no request of the command entry has the form of a
/// root call yet.
fn root_call(row: &Row) -> Disposition {
    Disposition::Compared(Err(format!(
        "the root call request `{}` has no request form yet",
        row.text("request")
    )))
}

// ---------------------------------------------------------------------------
// The comparison

/// An outcome as the `kind` and `result` columns name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Named {
    /// `ok`: an answer.
    Answer,
    /// A result state.
    State(MathState),
    /// An error kind.
    Error(ErrorKind),
}

/// The outcome named `name`, or `None` for a name that kalyx does not
/// define, such as a kind of a later release.
fn named(name: &str) -> Option<Named> {
    let fault = |kind| Named::Error(ErrorKind::Fault(kind));
    Some(match name {
        "ok" => Named::Answer,
        "Undecided" => Named::State(MathState::Undecided),
        "NotConverged" => Named::State(MathState::NotConverged),
        "ResourceLimit" => Named::Error(ErrorKind::ResourceLimit),
        "Cancelled" => Named::Error(ErrorKind::Cancelled),
        "DeadlineExceeded" => Named::Error(ErrorKind::DeadlineExceeded),
        "Syntax" => fault(FaultKind::Syntax),
        "UnknownSymbol" => fault(FaultKind::UnknownSymbol),
        "DivisionByZero" => fault(FaultKind::DivisionByZero),
        "NonIntegerExponent" => fault(FaultKind::NonIntegerExponent),
        "NotPolynomial" => fault(FaultKind::NotPolynomial),
        "Unsupported" => fault(FaultKind::Unsupported),
        "Internal" => fault(FaultKind::Internal),
        "OutsideDomain" => fault(FaultKind::OutsideDomain),
        "VariableMismatch" => fault(FaultKind::VariableMismatch),
        _ => return None,
    })
}

/// Limits far beyond every answer of the vectors, for reading, comparing
/// and displaying answers.
fn wide() -> Context {
    let limits = Limits::new()
        .with_max_work(u64::MAX)
        .with_max_depth(1 << 20)
        .with_max_nodes(1 << 40)
        .with_max_storage_bytes(1 << 40)
        .with_max_output_bytes(u64::MAX)
        .with_max_exponent(1 << 20)
        .with_max_integer_bits(1 << 20);
    Context::new(limits, CancelFlag::new())
}

/// The outcome as the vectors write it, for the report of a difference.
fn observed(outcome: &Outcome) -> String {
    match outcome.result() {
        Ok(Settled::Value(Answer::Term(term))) => match term.display(&mut wide()) {
            Ok(text) => format!("ok {text}"),
            Err(error) => format!("ok, whose display failed with {:?}", error.kind()),
        },
        Ok(Settled::State(state)) => format!("{state:?}"),
        Ok(other) => format!("{other:?}"),
        Err(error) => match (error.kind(), error.exceeded()) {
            (ErrorKind::ResourceLimit, Some(exceeded)) => {
                format!("ResourceLimit on {}", exceeded.id().name())
            }
            (ErrorKind::Fault(fault), _) => format!("{fault:?}"),
            (kind, _) => format!("{kind:?}"),
        },
    }
}

/// A frozen answer split into the text of its value, its condition after
/// ` where ` and its scope after ` assuming `, as an answer line holds them
/// in its fields TEXT, CONDITION and ASSUMPTIONS.
#[derive(Debug, PartialEq, Eq)]
struct Expected<'a> {
    /// The text of the value.
    text: &'a str,
    /// The condition, without ` where `.
    condition: Option<&'a str>,
    /// The scope, without ` assuming ` and its braces, written as the role
    /// `scope` is.
    assumptions: Option<String>,
}

/// The frozen answer `answer` split into its parts: a trailing
/// ` assuming {…}` is its scope, and then the text before the first
/// ` where ` is the text of its value and the rest its condition. The parts
/// are split only; the replay compares the text, and the condition and the
/// scope are compared with the answers whose kinds have them.
fn split_answer(answer: &str) -> Expected<'_> {
    let (rest, assumptions) = match answer.rsplit_once(" assuming ") {
        Some((rest, scope)) => match scope_argument(scope) {
            Some(scope) => (rest, Some(scope.unwrap_or_default())),
            None => (answer, None),
        },
        None => (answer, None),
    };
    let (text, condition) = match rest.split_once(" where ") {
        Some((text, condition)) => (text, Some(condition)),
        None => (rest, None),
    };
    Expected {
        text,
        condition,
        assumptions,
    }
}

/// Compares `outcome` with the expectation of a row: `result` names an
/// answer, a result state or an error kind; `answer` is the expected
/// answer, whose text is read with `parse` and compared with the value by
/// canonical form; and `field`, when the row sets one, is the field of
/// `Limits` that a `ResourceLimit` must name. Never compares display text
/// or work. Returns how they differ.
fn compare(
    result: &str,
    answer: Option<&str>,
    field: Option<LimitField>,
    outcome: &Outcome,
) -> Result<(), String> {
    let expected = match (result, answer) {
        ("ok", Some(answer)) => format!("ok {answer}"),
        _ => result.to_owned(),
    };
    let differ = |why: &str| format!("expected {expected}, observed {}{why}", observed(outcome));
    let Some(named) = named(result) else {
        return Err(differ(", and kalyx has no such outcome"));
    };
    match (named, outcome.result()) {
        (Named::Answer, Ok(Settled::Value(Answer::Term(term)))) => {
            let Some(answer) = answer else {
                return Err(differ(", and the row has no answer"));
            };
            let c = &mut wide();
            let expected = parse(split_answer(answer).text, c).map_err(|error| {
                differ(&format!(
                    ", and the answer fails to parse with {:?}",
                    error.kind()
                ))
            })?;
            match term.equals(&expected, c) {
                Ok(true) => Ok(()),
                Ok(false) => Err(differ("")),
                Err(error) => Err(differ(&format!(
                    ", and the comparison failed with {:?}",
                    error.kind()
                ))),
            }
        }
        (Named::Answer, Ok(Settled::Value(_))) => Err(differ(
            ", and no comparison exists yet for this kind of value",
        )),
        (Named::State(state), Ok(Settled::State(found))) if state == *found => Ok(()),
        (Named::Error(kind), Err(error)) if error.kind() == kind => match field {
            Some(field)
                if kind == ErrorKind::ResourceLimit
                    && error.exceeded().map(LimitExceeded::id) != Some(&LimitId::Field(field)) =>
            {
                Err(differ(&format!(
                    ", where the row sets {}",
                    LimitId::Field(field).name()
                )))
            }
            _ => Ok(()),
        },
        _ => Err(differ("")),
    }
}

// ---------------------------------------------------------------------------
// The tests

// Every slice selects the rows that it states, every command, request,
// operation and input that it names selects at least one row, every
// operation maps to a command of its slice, and no row is in two slices.
#[test]
fn every_slice_selects_its_rows_and_no_row_is_in_two_slices() {
    let vectors = vectors();
    let mut names = BTreeSet::new();
    let mut selected = BTreeSet::new();
    for slice in &SLICES {
        assert!(names.insert(slice.name), "{}", slice.name);
        let selection = select(slice, vectors);
        assert_eq!(selection.rows(), slice.rows, "{}", slice.name);
        for command in slice.commands {
            assert!(
                selection
                    .cli
                    .iter()
                    .any(|row| row.text("command") == *command),
                "{}: {command}",
                slice.name
            );
        }
        for request in slice.requests {
            assert!(
                selection
                    .root_calls
                    .iter()
                    .any(|row| row.text("request") == *request),
                "{}: {request}",
                slice.name
            );
        }
        for operation in slice.operations {
            assert!(
                slice.commands.contains(&operation.command),
                "{}",
                operation.name
            );
            for input in operation.inputs {
                assert!(
                    selection.library.iter().any(|(chosen, row)| {
                        chosen.name == operation.name && row.text("input") == *input
                    }),
                    "{}: {}: {input}",
                    slice.name,
                    operation.name
                );
            }
        }
        let ids = selection
            .cli
            .iter()
            .map(|row| (CLI_CASES.name, row.text("id")))
            .chain(
                selection
                    .library
                    .iter()
                    .map(|(_, row)| (LIBRARY.name, row.text("id"))),
            )
            .chain(
                selection
                    .root_calls
                    .iter()
                    .map(|row| (ROOT_CALLS.name, row.text("id"))),
            );
        for id in ids {
            assert!(selected.insert(id), "{id:?} is in two slices");
        }
    }
    assert_eq!(selected.len(), 160 + 9_853 + 972);
}

// The rows of no slice in the three files are the sessions of the line mode
// and the rows of the commands, requests and inputs that no slice names: the
// other command-line cases, the expansions of the inputs that are not
// polynomials, and the root calls of five requests.
#[test]
fn the_rows_of_no_slice_are_the_sessions_and_the_unnamed_rows() {
    /// The rows of `rows` whose id is not in `ids`.
    fn outside<'v>(rows: &'v [Row], ids: &BTreeSet<&str>) -> Vec<&'v Row> {
        rows.iter()
            .filter(|row| !ids.contains(row.text("id")))
            .collect()
    }
    let vectors = vectors();
    let mut ids: [BTreeSet<&str>; 3] = Default::default();
    for slice in &SLICES {
        let selection = select(slice, vectors);
        ids[0].extend(selection.cli.iter().map(|row| row.text("id")));
        ids[1].extend(selection.library.iter().map(|(_, row)| row.text("id")));
        ids[2].extend(selection.root_calls.iter().map(|row| row.text("id")));
    }
    let cli = outside(&vectors.cli, &ids[0]);
    let library = outside(&vectors.library, &ids[1]);
    let root_calls = outside(&vectors.root_calls, &ids[2]);
    let sessions = cli
        .iter()
        .filter(|row| row.get("command") == Some("repl"))
        .count();
    assert_eq!(
        [
            sessions,
            cli.len() - sessions,
            library.len(),
            root_calls.len()
        ],
        [15, 227, 2_720, 810]
    );
    let operations: BTreeSet<&str> = library.iter().map(|row| row.text("operation")).collect();
    assert_eq!(operations, BTreeSet::from(["expand"]));
    let inputs: BTreeSet<&str> = library.iter().map(|row| row.text("input")).collect();
    assert_eq!(inputs.len(), 85);
    assert!(
        inputs
            .iter()
            .all(|input| !POLYNOMIAL_INPUTS.contains(input))
    );
    let requests: BTreeSet<&str> = root_calls.iter().map(|row| row.text("request")).collect();
    assert_eq!(
        requests,
        BTreeSet::from([
            "approximate -8",
            "approximate 2",
            "integral",
            "limit +inf",
            "limit 0+",
        ])
    );
}

// The registration of a command is read from the command entry: the three
// operations of release 0.1 are registered, and names that the dispatch
// table does not hold are not.
#[test]
fn a_command_is_registered_when_the_command_entry_runs_it() {
    for command in ["eval", "expand", "diff"] {
        assert!(registered(command), "{command}");
    }
    for command in ["", "EVAL", "expand ", "no-such-command"] {
        assert!(!registered(command), "{command:?}");
    }
}

// Every row of an enabled slice that the replay compares has the outcome
// that it records. Of the 9 cases of `eval`, 2 are usage errors; of
// the 256 polynomial expansions of the library, 96 have the full budget,
// the budget 0 or a cancelled flag, and 160 depend on how work is counted.
#[test]
fn the_rows_of_the_enabled_slices_replay_without_a_difference() {
    let vectors = vectors();
    let mut enabled_slices = Vec::new();
    let mut differences = Vec::new();
    for slice in SLICES.iter().filter(|slice| enabled(slice)) {
        let replay = replay(&select(slice, vectors));
        enabled_slices.push((slice.name, replay.compared, replay.usage, replay.budget));
        differences.extend(replay.differences);
    }
    assert!(
        differences.is_empty(),
        "{} differences:\n{}",
        differences.len(),
        differences.join("\n")
    );
    assert_eq!(
        enabled_slices,
        [("exact_numbers", 7, 2, 0), ("polynomials", 5 + 96, 0, 160)]
    );
}

// The slices whose commands the dispatch table does not register yet are
// pending; their rows are counted and printed, not replayed.
#[test]
fn the_pending_slices_are_counted() {
    let vectors = vectors();
    let mut pending = Vec::new();
    let mut rows = [0; 3];
    for slice in SLICES.iter().filter(|slice| !enabled(slice)) {
        let counts = select(slice, vectors).rows();
        println!(
            "pending slice {}: {} command-line cases, {} library observations, {} root calls",
            slice.name, counts[0], counts[1], counts[2]
        );
        for (total, count) in rows.iter_mut().zip(counts) {
            *total += count;
        }
        pending.push(slice.name);
    }
    println!(
        "{} pending slices: {} command-line cases, {} library observations, {} root calls",
        pending.len(),
        rows[0],
        rows[1],
        rows[2]
    );
    assert_eq!(
        pending,
        [
            "function_expressions",
            "questions_and_refinement",
            "substitution",
            "function_derivatives",
            "series",
            "univariate_polynomials",
            "univariate_factorization",
            "multivariate_polynomials",
            "real_roots",
            "real_algebraic_numbers",
            "complex_algebraic_numbers",
            "number_fields",
            "real_sets_and_inequalities",
        ]
    );
    assert_eq!(rows, [146, 9_597, 972]);
}

// A library observation that needs an operand which a request of release
// 0.1 could not express, the scope of a scoped operation or an operand of
// its command, becomes a request with entries of the operand table: the
// scope `pos` the entry `scope` with `x: positive`, the property of `f-ask`
// and the order of `f-diff` the entries of their roles. Run now, each is a
// difference of its row, since the dispatch table does not hold its
// command, which fails before its table is read.
#[test]
fn an_observation_that_a_request_cannot_express_is_a_difference() {
    let vectors = vectors();
    let operation = |slice_name: &str, name: &str| -> &'static Operation {
        slice(slice_name)
            .operations
            .iter()
            .find(|operation| operation.name == name)
            .unwrap()
    };
    let cases = [
        (
            operation("function_expressions", "parse"),
            "i90_pos_parse_w1000000",
            Request::new("fexpr", "x", "x").with_operand("scope", "x: positive"),
            "expected ok x, observed Unsupported",
        ),
        (
            operation("questions_and_refinement", "ask"),
            "i90_none_ask_w1000000",
            Request::new("f-ask", "x", "x").with_operand("property", "positive"),
            "expected ok unknown, observed Unsupported",
        ),
        (
            operation("function_derivatives", "diff"),
            "i90_none_diff_w1000000",
            Request::new("f-diff", "x", "x").with_operand("order", "1"),
            "expected ok 1, observed Unsupported",
        ),
    ];
    for (operation, id, request, difference) in cases {
        let row = vectors
            .library
            .iter()
            .find(|row| row.text("id") == id)
            .unwrap();
        assert_eq!(observation_request(operation, row), request, "{id}");
        let Disposition::Compared(Err(found)) = observation(operation, row) else {
            panic!("{id} is not a difference");
        };
        assert_eq!(found, difference, "{id}");
    }
    // The polynomial expansion reads no scope: its row in the scope `pos`
    // is the request of the scope `none`.
    let expand = operation("polynomials", "expand");
    let row = vectors
        .library
        .iter()
        .find(|row| row.text("id") == "i08_pos_expand_w1000000")
        .unwrap();
    assert_eq!(
        observation_request(expand, row),
        Request::new("expand", "x", row.text("input"))
    );
}

// The frozen requests and answers become the fields and roles of release
// 0.2: a ring argument of a command-line case becomes the entries of the
// roles `variables` and `monomial_order`, a scope argument the entry of the
// role `scope`, and a case with more than one argument after them stays a
// difference; a frozen answer splits into its text, its condition after
// ` where ` and its scope after ` assuming `. The two slices of these cases
// are pending, so the replay does not run them, and this test checks what
// it builds.
#[test]
fn frozen_conditions_scopes_and_rings_become_fields_and_roles() {
    let vectors = vectors();
    let case = |id: &str| -> &Row {
        vectors
            .cli
            .iter()
            .find(|row| row.text("id") == id)
            .unwrap_or_else(|| panic!("no case {id}"))
    };
    let Ok((request, limits, field)) = cli_request(case("algebra/mpoly-expands-square")) else {
        panic!("the ring case is a request");
    };
    assert_eq!(
        request,
        Request::new("mpoly", "x", "(x+y)^2")
            .with_operand("variables", "x, y")
            .with_operand("monomial_order", "lex")
    );
    assert_eq!((limits, field), (Limits::new(), None));
    let Ok((request, _, _)) = cli_request(case("symbolic/f-refine-uses-positivity")) else {
        panic!("the scope case is a request");
    };
    assert_eq!(
        request,
        Request::new("f-refine", "x", "sqrt(x^2)").with_operand("scope", "x: positive")
    );
    let Err(Disposition::Compared(Err(difference))) =
        cli_request(case("algebra/mdiff-partial-derivative"))
    else {
        panic!("a case with two arguments after its ring is a difference");
    };
    assert_eq!(difference, "2 operands, where a request has one input");
    assert_eq!(
        split_answer("x where is_nonzero(x)"),
        Expected {
            text: "x",
            condition: Some("is_nonzero(x)"),
            assumptions: None,
        }
    );
    assert_eq!(
        split_answer("x assuming {x:positive}"),
        Expected {
            text: "x",
            condition: None,
            assumptions: Some("x: positive".to_owned()),
        }
    );
    assert_eq!(
        split_answer("8*x^3"),
        Expected {
            text: "8*x^3",
            condition: None,
            assumptions: None,
        }
    );
    // Other braces are no scope, and the empty scope gives no entry.
    assert_eq!(scope_argument("{ 1 }"), None);
    assert_eq!(scope_argument("{}"), Some(None));
    assert_eq!(
        scope_argument("{x:real,y:positive}"),
        Some(Some("x: real, y: positive".to_owned()))
    );
    assert_eq!(
        ring_argument("Q[]:lex"),
        Some((String::new(), "lex".to_owned()))
    );
}

/// The bytes of `file` with the field `column` of the row `id` set to
/// `value`.
fn corrupted(file: &File, id: &str, column: &str, value: &str) -> Vec<u8> {
    let index = file
        .columns
        .iter()
        .position(|known| *known == column)
        .unwrap();
    let mut found = 0;
    let text: String = std::str::from_utf8(file.bytes)
        .unwrap()
        .split_terminator('\n')
        .map(|line| {
            let mut fields: Vec<&str> = line.split('\t').collect();
            if fields[0] == id {
                fields[index] = value;
                found += 1;
            }
            format!("{}\n", fields.join("\t"))
        })
        .collect();
    assert_eq!(found, 1, "{id}");
    text.into_bytes()
}

// The replay fails when one expectation of an enabled slice is corrupted:
// the answer of a polynomial expansion, the error kind of a command-line
// case and the request failure of a cancelled request, each in a copy of
// its file, read and replayed the same way. Each corruption gives exactly
// one difference, at its row.
#[test]
fn a_corrupted_expectation_fails_the_replay() {
    let polynomials = slice("polynomials");
    assert!(
        replay(&select(polynomials, vectors()))
            .differences
            .is_empty()
    );
    let cases = [
        (
            Vectors::read(
                CLI_CASES.bytes,
                &corrupted(
                    &LIBRARY,
                    "i08_none_expand_w1000000",
                    "answer",
                    "(4*(x)^(3))",
                ),
                ROOT_CALLS.bytes,
            ),
            "library.tsv i08_none_expand_w1000000: expected ok (4*(x)^(3)), observed ok 8*x^3",
        ),
        (
            Vectors::read(
                &corrupted(
                    &CLI_CASES,
                    "algebra/expand-rejects-polynomial-division",
                    "kind",
                    "UnknownSymbol",
                ),
                LIBRARY.bytes,
                ROOT_CALLS.bytes,
            ),
            "cli_cases.tsv algebra/expand-rejects-polynomial-division: expected UnknownSymbol, observed NotPolynomial",
        ),
        (
            Vectors::read(
                CLI_CASES.bytes,
                &corrupted(
                    &LIBRARY,
                    "i13_neg_expand_cancelled",
                    "result",
                    "ResourceLimit",
                ),
                ROOT_CALLS.bytes,
            ),
            "library.tsv i13_neg_expand_cancelled: expected ResourceLimit, observed Cancelled",
        ),
    ];
    for (corrupted, difference) in cases {
        let replay = replay(&select(polynomials, &corrupted));
        assert_eq!(replay.differences, [difference]);
    }
}
