//! Format checks for the answer vectors in `vectors/r02.tsv`: seven columns,
//! unique ids, results from the fixed table of result kinds and limits named
//! by `Limits` fields. `vectors/README.md` describes the format.

use std::collections::BTreeSet;

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
