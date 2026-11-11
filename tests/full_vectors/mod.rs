//! The six files of the full vectors in `vectors/` and the reader of their
//! plain TSV, shared by `tests/vectors.rs`, which checks the format of the
//! files, and `tests/slices.rs`, which replays their slices.
//! `vectors/README.md` describes the files, their columns and the escaping
//! of their fields.

/// One file of the full vectors.
pub struct File {
    /// The name of the file in `vectors/`.
    pub name: &'static str,
    /// The bytes of the file, embedded when the test is built.
    pub bytes: &'static [u8],
    /// The columns of its header row, in order.
    pub columns: &'static [&'static str],
    /// The number of its rows after the header row.
    pub rows: usize,
}

/// The command-line cases.
pub const CLI_CASES: File = File {
    name: "cli_cases.tsv",
    bytes: include_bytes!("../../vectors/cli_cases.tsv"),
    columns: &[
        "id", "source", "command", "args", "stdin", "status", "stdout", "stderr", "kind",
    ],
    rows: 402,
};

/// The inventory of the integration tests.
pub const INTEGRATION_TESTS: File = File {
    name: "integration_tests.tsv",
    bytes: include_bytes!("../../vectors/integration_tests.tsv"),
    columns: &[
        "id", "file", "module", "test", "category", "commands", "ignored", "status", "blob",
    ],
    rows: 968,
};

/// The library observations.
pub const LIBRARY: File = File {
    name: "library.tsv",
    bytes: include_bytes!("../../vectors/library.tsv"),
    columns: &[
        "id",
        "scope",
        "operation",
        "input",
        "limits",
        "cancelled",
        "result",
        "answer",
    ],
    rows: 12_573,
};

/// The terminal session.
pub const TERMINAL_SESSION: File = File {
    name: "terminal_session.tsv",
    bytes: include_bytes!("../../vectors/terminal_session.tsv"),
    columns: &["id", "input", "output"],
    rows: 471,
};

/// The terminal session of collection values.
pub const TERMINAL_COLLECTIONS: File = File {
    name: "terminal_collections.tsv",
    bytes: include_bytes!("../../vectors/terminal_collections.tsv"),
    columns: &["id", "input", "output"],
    rows: 35,
};

/// The root calls.
pub const ROOT_CALLS: File = File {
    name: "root_calls.tsv",
    bytes: include_bytes!("../../vectors/root_calls.tsv"),
    columns: &["id", "scope", "request", "source", "result", "answer"],
    rows: 1_782,
};

/// The six files, in the order of the table of files in `vectors/README.md`.
pub const FILES: [&File; 6] = [
    &CLI_CASES,
    &INTEGRATION_TESTS,
    &LIBRARY,
    &TERMINAL_SESSION,
    &TERMINAL_COLLECTIONS,
    &ROOT_CALLS,
];

/// Reads `bytes` as plain TSV and returns its lines, the header row first,
/// each split at its tabs into its fields, as they are written. The bytes
/// must be UTF-8 text whose every line ends with a line feed; no line may be
/// empty or start with `#`, and every field must be a written value that
/// [`decode`] accepts. Returns the first place that breaks these rules.
pub fn lines(bytes: &[u8]) -> Result<Vec<Vec<&str>>, String> {
    let text = std::str::from_utf8(bytes)
        .map_err(|error| format!("not UTF-8 after byte {}", error.valid_up_to()))?;
    let Some(body) = text.strip_suffix('\n') else {
        return Err("the last line does not end with a line feed".to_owned());
    };
    let mut lines = Vec::new();
    for (index, line) in body.split('\n').enumerate() {
        let at = index + 1;
        if line.is_empty() {
            return Err(format!("line {at}: an empty line"));
        }
        if line.starts_with('#') {
            return Err(format!("line {at}: a comment line"));
        }
        let fields: Vec<&str> = line.split('\t').collect();
        for (column, field) in fields.iter().enumerate() {
            decode(field).map_err(|error| format!("line {at}, column {}: {error}", column + 1))?;
        }
        lines.push(fields);
    }
    Ok(lines)
}

/// The value of a field as it is written: `None` for `-`, which holds no
/// value or the empty text, and otherwise the text with its escapes
/// replaced. A field is never empty; `\-` is the value `-` and valid only
/// as a whole field; a backslash starts `\\`, `\t`, `\n`, `\r` or `\x` with
/// two lowercase hexadecimal digits of a control byte other than tab, line
/// feed and carriage return; and a control byte is never written as it is.
pub fn decode(field: &str) -> Result<Option<String>, String> {
    match field {
        "" => return Err("an empty field".to_owned()),
        "-" => return Ok(None),
        "\\-" => return Ok(Some("-".to_owned())),
        _ => {}
    }
    let mut value = String::with_capacity(field.len());
    let mut chars = field.chars();
    while let Some(c) = chars.next() {
        if is_control(c) {
            return Err(format!(
                "the control byte {:#04x} is not escaped",
                u32::from(c)
            ));
        }
        if c != '\\' {
            value.push(c);
            continue;
        }
        let escaped = match chars.next() {
            Some('\\') => '\\',
            Some('t') => '\t',
            Some('n') => '\n',
            Some('r') => '\r',
            Some('x') => hex_escape(chars.next(), chars.next())?,
            Some('-') => return Err("`\\-` is valid only as a whole field".to_owned()),
            _ => return Err("a backslash that starts no escape".to_owned()),
        };
        value.push(escaped);
    }
    Ok(Some(value))
}

/// Whether `c` is a byte from `0x00` to `0x1F` or `0x7F`.
fn is_control(c: char) -> bool {
    c <= '\u{1f}' || c == '\u{7f}'
}

/// The control byte of the escape `\x` followed by `high` and `low`.
fn hex_escape(high: Option<char>, low: Option<char>) -> Result<char, String> {
    let digit = |c: Option<char>| match c {
        Some(c @ ('0'..='9' | 'a'..='f')) => c.to_digit(16),
        _ => None,
    };
    let (Some(high), Some(low)) = (digit(high), digit(low)) else {
        return Err("`\\x` needs two lowercase hexadecimal digits".to_owned());
    };
    match char::from_u32(high * 16 + low) {
        Some(c) if is_control(c) && !matches!(c, '\t' | '\n' | '\r') => Ok(c),
        _ => Err(format!(
            "`\\x{high:x}{low:x}` is not the escape of a control byte without its own escape"
        )),
    }
}
