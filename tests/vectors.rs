//! Format checks for the answer vectors in `vectors/r02.tsv`: seven columns,
//! unique ids, results from the fixed table of result kinds and limits named
//! by `Limits` fields. Format checks for the six files of the full vectors:
//! plain TSV, the header row, the columns of every row, unique ids and the
//! number of rows. `vectors/README.md` describes the formats.

#![allow(
    clippy::unwrap_used,
    reason = "the helpers of the negative tests unwrap the embedded files and the rejections, as the tests do"
)]

mod full_vectors;

use std::collections::BTreeSet;

use full_vectors::{FILES, File};

const VECTORS: &str = include_str!("../vectors/r02.tsv");

/// The fixed table of values of the `result` column.
const RESULTS: [&str; 11] = [
    "ok",
    "ResourceLimit",
    "Cancelled",
    "DeadlineExceeded",
    "Syntax",
    "UnknownSymbol",
    "DivisionByZero",
    "NonIntegerExponent",
    "NotPolynomial",
    "Unsupported",
    "Internal",
];

const OPERATIONS: [&str; 3] = ["eval", "expand", "diff"];

/// The header row, which is the first line of the file.
const HEADER: &str = "id\toperation\tvariable\tinput\tresult\tanswer\tlimits";

/// The fields of `Limits` that the `limits` column may set.
const LIMIT_FIELDS: [&str; 9] = [
    "max_work",
    "max_input_bytes",
    "max_output_bytes",
    "max_depth",
    "max_nodes",
    "max_storage_bytes",
    "max_integer_bits",
    "max_exponent",
    "max_frames",
];

/// One case of the vector file.
#[derive(Debug)]
struct Case<'a> {
    id: &'a str,
    result: &'a str,
    limits: Vec<(&'a str, u64)>,
}

/// Reads the `limits` column: `-`, or `field=value` settings separated by `;`.
fn limits(column: &str) -> Result<Vec<(&str, u64)>, String> {
    if column == "-" {
        return Ok(Vec::new());
    }
    let mut settings = Vec::new();
    for setting in column.split(';') {
        let Some((field, value)) = setting.split_once('=') else {
            return Err(format!("limit setting without '=': {setting}"));
        };
        if !LIMIT_FIELDS.contains(&field) {
            return Err(format!("unknown Limits field: {field}"));
        }
        if settings.iter().any(|(seen, _)| *seen == field) {
            return Err(format!("Limits field set twice: {field}"));
        }
        let value = value
            .parse::<u64>()
            .map_err(|_| format!("limit value is not a u64: {setting}"))?;
        settings.push((field, value));
    }
    Ok(settings)
}

/// Reads a vector file, rejecting the first line that breaks the format. The
/// file is plain TSV: the header row, then one case per line, with no comment
/// or empty lines, so that any TSV reader takes the first line as the header.
fn cases(text: &str) -> Result<Vec<Case<'_>>, String> {
    let mut lines = text.lines().enumerate();
    match lines.next() {
        Some((_, line)) if line == HEADER => {}
        _ => return Err("line 1: expected the header row".to_owned()),
    }
    let mut ids = BTreeSet::new();
    let mut cases = Vec::new();
    for (index, line) in lines {
        let at = format!("line {}", index + 1);
        if line.is_empty() || line.starts_with('#') {
            return Err(format!("{at}: an empty or comment line"));
        }
        let columns: Vec<&str> = line.split('\t').collect();
        let [id, operation, variable, _input, result, answer, limit] = columns.as_slice() else {
            return Err(format!("{at}: {} columns instead of 7", columns.len()));
        };
        if columns.iter().any(|column| column.is_empty()) {
            return Err(format!("{at}: an empty column"));
        }
        if !ids.insert(*id) {
            return Err(format!("{at}: duplicate id {id}"));
        }
        if !OPERATIONS.contains(operation) {
            return Err(format!("{at}: unknown operation {operation}"));
        }
        if variable.chars().any(|c| !c.is_ascii_alphabetic()) {
            return Err(format!("{at}: invalid variable {variable}"));
        }
        if !RESULTS.contains(result) {
            return Err(format!("{at}: unknown result kind {result}"));
        }
        if (*result == "ok") == (*answer == "-") {
            return Err(format!(
                "{at}: an ok case needs an answer and an error case `-`"
            ));
        }
        let limits = limits(limit).map_err(|message| format!("{at}: {message}"))?;
        if *result == "ResourceLimit" && limits.is_empty() {
            return Err(format!("{at}: a ResourceLimit case must state its limit"));
        }
        cases.push(Case { id, result, limits });
    }
    Ok(cases)
}

#[test]
fn the_vectors_have_the_documented_format() {
    let cases = cases(VECTORS).unwrap();
    assert_eq!(cases.len(), 58);
    assert_eq!(cases.iter().filter(|case| case.result == "ok").count(), 49);
    let limited: Vec<_> = cases
        .iter()
        .filter(|case| !case.limits.is_empty())
        .map(|case| (case.id, case.limits.clone()))
        .collect();
    assert_eq!(
        limited,
        [
            ("degree_limit_1", vec![("max_exponent", 256)]),
            ("bit_limit_1", vec![("max_integer_bits", 4096)]),
            ("depth_limit_1", vec![("max_depth", 128)]),
            ("right_depth_limit_1", vec![("max_depth", 32)]),
        ]
    );
}

#[test]
fn rejects_a_case_with_six_columns() {
    let error = cases(&with_header("a\teval\tx\t1\tok\t1\n")).unwrap_err();
    assert!(error.contains("6 columns instead of 7"), "{error}");
}

#[test]
fn rejects_a_result_kind_outside_the_table() {
    let error = cases(&with_header("a\teval\tx\t1/0\tDivideByZero\t-\t-\n")).unwrap_err();
    assert!(
        error.contains("unknown result kind DivideByZero"),
        "{error}"
    );
}

#[test]
fn rejects_a_duplicate_id_and_an_unknown_limit_field() {
    let duplicate = cases(&with_header(
        "a\teval\tx\t1\tok\t1\t-\na\teval\tx\t2\tok\t2\t-\n",
    ))
    .unwrap_err();
    assert!(duplicate.contains("duplicate id a"), "{duplicate}");
    let field = cases(&with_header(
        "a\texpand\tx\tx^9\tResourceLimit\t-\tmax_degree=8\n",
    ))
    .unwrap_err();
    assert!(
        field.contains("unknown Limits field: max_degree"),
        "{field}"
    );
}

#[test]
fn rejects_an_answer_that_does_not_match_the_result() {
    let error = cases(&with_header("a\teval\tx\t1/0\tDivisionByZero\t0\t-\n")).unwrap_err();
    assert!(error.contains("an ok case needs an answer"), "{error}");
}

#[test]
fn rejects_a_resource_limit_case_without_its_limit() {
    let error = cases(&with_header("a\texpand\tx\tx^9\tResourceLimit\t-\t-\n")).unwrap_err();
    assert!(error.contains("must state its limit"), "{error}");
}

/// Puts the header row in front of the case lines of a negative example.
fn with_header(cases: &str) -> String {
    format!("{HEADER}\n{cases}")
}

#[test]
fn rejects_a_missing_commented_or_late_header() {
    let missing = cases("a\teval\tx\t1\tok\t1\t-\n").unwrap_err();
    assert!(
        missing.contains("line 1: expected the header row"),
        "{missing}"
    );
    let commented = cases(&format!("# {HEADER}\na\teval\tx\t1\tok\t1\t-\n")).unwrap_err();
    assert!(
        commented.contains("line 1: expected the header row"),
        "{commented}"
    );
    let late = cases(&format!("# sources\n{HEADER}\n")).unwrap_err();
    assert!(late.contains("line 1: expected the header row"), "{late}");
}

#[test]
fn rejects_comment_and_empty_lines_after_the_header() {
    let comment = cases(&with_header("# a note\na\teval\tx\t1\tok\t1\t-\n")).unwrap_err();
    assert!(
        comment.contains("line 2: an empty or comment line"),
        "{comment}"
    );
    let empty = cases(&with_header("\na\teval\tx\t1\tok\t1\t-\n")).unwrap_err();
    assert!(
        empty.contains("line 2: an empty or comment line"),
        "{empty}"
    );
}

// ---------------------------------------------------------------------------
// The full vectors

/// The five format checks of a file of the full vectors, in this order:
/// `plain TSV`, the reading of `full_vectors::lines`; `header`, the header
/// row names the columns of the file; `columns`, every row has as many
/// columns as the header; `ids`, the ids in the first column are unique;
/// and `rows`, the file has the number of rows that `vectors/README.md`
/// states. Returns the number of rows, or the first check that fails, named
/// after the file.
fn check_full(file: &File, bytes: &[u8]) -> Result<usize, String> {
    let name = file.name;
    let lines =
        full_vectors::lines(bytes).map_err(|error| format!("{name}: plain TSV: {error}"))?;
    let Some((header, rows)) = lines.split_first() else {
        return Err(format!("{name}: header: no header row"));
    };
    if header.as_slice() != file.columns {
        return Err(format!(
            "{name}: header: the header row is not {}",
            file.columns.join(" ")
        ));
    }
    for (index, row) in rows.iter().enumerate() {
        if row.len() != file.columns.len() {
            return Err(format!(
                "{name}: columns: line {}: {} columns instead of {}",
                index + 2,
                row.len(),
                file.columns.len()
            ));
        }
    }
    let mut ids = BTreeSet::new();
    for (index, row) in rows.iter().enumerate() {
        if !ids.insert(row[0]) {
            return Err(format!(
                "{name}: ids: line {}: duplicate id {}",
                index + 2,
                row[0]
            ));
        }
    }
    if rows.len() != file.rows {
        return Err(format!(
            "{name}: rows: {} rows instead of {}",
            rows.len(),
            file.rows
        ));
    }
    Ok(rows.len())
}

/// The text of `file` with its line `index`, counted from 0 at the header
/// row, replaced by what `change` makes of it.
fn changed_line(file: &File, index: usize, change: impl Fn(&str) -> String) -> String {
    let text = std::str::from_utf8(file.bytes).unwrap();
    let mut lines: Vec<String> = text.split_terminator('\n').map(str::to_owned).collect();
    lines[index] = change(&lines[index]);
    lines.iter().map(|line| format!("{line}\n")).collect()
}

/// Asserts that the format checks reject `bytes`, a corrupted copy of
/// `file`, in the check `check`, with an error that contains `detail`.
fn assert_rejected(file: &File, bytes: &[u8], check: &str, detail: &str) {
    let error = check_full(file, bytes).unwrap_err();
    assert!(
        error.starts_with(&format!("{}: {check}: ", file.name)),
        "{error}"
    );
    assert!(error.contains(detail), "{error}");
}

// Each of the six files passes the five checks and has the number of rows
// that `vectors/README.md` states.
#[test]
fn the_full_vectors_have_the_documented_format() {
    let rows: Vec<(&str, usize)> = FILES
        .iter()
        .map(|file| (file.name, check_full(file, file.bytes).unwrap()))
        .collect();
    assert_eq!(
        rows,
        [
            ("cli_cases.tsv", 402),
            ("integration_tests.tsv", 968),
            ("library.tsv", 12_573),
            ("terminal_session.tsv", 471),
            ("terminal_collections.tsv", 35),
            ("root_calls.tsv", 1_782),
        ]
    );
}

// The plain TSV check rejects a copy of each file with a byte that is not
// UTF-8, a comment line, an empty line, an empty field, a control byte that
// is not escaped, a backslash that starts no escape, or a last line without
// its line feed.
#[test]
fn rejects_a_full_vector_file_that_is_not_plain_tsv() {
    for file in FILES {
        let mut bytes = file.bytes.to_vec();
        let second = file.bytes.iter().position(|&byte| byte == b'\n').unwrap() + 1;
        bytes.insert(second, 0xff);
        assert_rejected(file, &bytes, "plain TSV", "not UTF-8");
        let comment = changed_line(file, 1, |line| format!("# {line}"));
        assert_rejected(
            file,
            comment.as_bytes(),
            "plain TSV",
            "line 2: a comment line",
        );
        let empty = changed_line(file, 1, |line| format!("\n{line}"));
        assert_rejected(file, empty.as_bytes(), "plain TSV", "line 2: an empty line");
        let field = changed_line(file, 1, |line| line.replacen('\t', "\t\t", 1));
        assert_rejected(
            file,
            field.as_bytes(),
            "plain TSV",
            "line 2, column 2: an empty field",
        );
        let control = changed_line(file, 1, |line| line.replacen('\t', "\t\r", 1));
        assert_rejected(
            file,
            control.as_bytes(),
            "plain TSV",
            "line 2, column 2: the control byte 0x0d is not escaped",
        );
        let escape = changed_line(file, 1, |line| format!("{line}\\q"));
        assert_rejected(
            file,
            escape.as_bytes(),
            "plain TSV",
            "a backslash that starts no escape",
        );
        let unterminated = &file.bytes[..file.bytes.len() - 1];
        assert_rejected(
            file,
            unterminated,
            "plain TSV",
            "the last line does not end with a line feed",
        );
    }
}

// The header check rejects a copy of each file whose header row renames its
// first column or leaves out its last one.
#[test]
fn rejects_a_full_vector_file_with_another_header_row() {
    for file in FILES {
        let renamed = changed_line(file, 0, |line| line.replacen("id", "name", 1));
        assert_rejected(
            file,
            renamed.as_bytes(),
            "header",
            "the header row is not id ",
        );
        let short = changed_line(file, 0, |line| line.rsplit_once('\t').unwrap().0.to_owned());
        assert_rejected(file, short.as_bytes(), "header", "the header row is not");
    }
}

// The column check rejects a copy of each file with a row that leaves out
// its last field or adds one.
#[test]
fn rejects_a_full_vector_file_with_a_row_of_other_columns() {
    for file in FILES {
        let columns = file.columns.len();
        let short = changed_line(file, 2, |line| line.rsplit_once('\t').unwrap().0.to_owned());
        assert_rejected(
            file,
            short.as_bytes(),
            "columns",
            &format!("line 3: {} columns instead of {columns}", columns - 1),
        );
        let long = changed_line(file, 2, |line| format!("{line}\t-"));
        assert_rejected(
            file,
            long.as_bytes(),
            "columns",
            &format!("line 3: {} columns instead of {columns}", columns + 1),
        );
    }
}

// The id check rejects a copy of each file whose third line has the id of
// the second.
#[test]
fn rejects_a_full_vector_file_with_a_duplicate_id() {
    for file in FILES {
        let text = std::str::from_utf8(file.bytes).unwrap();
        let first = text.split('\n').nth(1).unwrap().split('\t').next().unwrap();
        let duplicate = changed_line(file, 2, |line| {
            let (_, rest) = line.split_once('\t').unwrap();
            format!("{first}\t{rest}")
        });
        assert_rejected(
            file,
            duplicate.as_bytes(),
            "ids",
            &format!("line 3: duplicate id {first}"),
        );
    }
}

// The row check rejects a copy of each file without its last row, and one
// with an extra row under a new id.
#[test]
fn rejects_a_full_vector_file_with_another_number_of_rows() {
    for file in FILES {
        let text = std::str::from_utf8(file.bytes).unwrap();
        let (rest, last) = text.strip_suffix('\n').unwrap().rsplit_once('\n').unwrap();
        let shorter = format!("{rest}\n");
        assert_rejected(
            file,
            shorter.as_bytes(),
            "rows",
            &format!("{} rows instead of {}", file.rows - 1, file.rows),
        );
        let (_, fields) = last.split_once('\t').unwrap();
        let longer = format!("{text}an_extra_row\t{fields}\n");
        assert_rejected(
            file,
            longer.as_bytes(),
            "rows",
            &format!("{} rows instead of {}", file.rows + 1, file.rows),
        );
    }
}
