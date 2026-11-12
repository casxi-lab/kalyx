//! The public names of the crate root: a scan of `src/lib.rs` derives them,
//! and they must be exactly the names that `api/root-names.txt` lists, so a
//! public name is never added to the crate root, removed or renamed without
//! the list changing with it. The public API conventions state which names
//! belong to the crate root.
//!
//! The scan reads the Rust source of `src/lib.rs` as tokens, skipping
//! comments, string and character literals and attributes, and takes every
//! item at the top level of the file whose visibility is plain `pub`: the
//! name of a module, function, type, trait, constant or static, and the names
//! that a `pub use` declaration brings into the crate root, with their
//! renamings. A glob re-export cannot be listed and fails the scan. A macro
//! exported with `#[macro_export]` lands in the crate root from whichever
//! module defines it, so a second test reads every Rust file under `src/`
//! and fails when one of them exports a macro. A public name that a macro of
//! `src/lib.rs` generates is not seen; the crate root has no such macro.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::panic,
    reason = "the helpers of the tests unwrap their results, as the tests do"
)]

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

const LIB: &str = include_str!("../src/lib.rs");

const LIST: &str = include_str!("../api/root-names.txt");

/// A token of Rust source: an identifier or a punctuation character.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Identifier(String),
    Punct(char),
}

/// The tokens of `source`, without comments and literals; a literal is
/// left out entirely, since no name of the crate root is one.
fn tokens(source: &str) -> Result<Vec<Token>, String> {
    let characters: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < characters.len() {
        let character = characters[index];
        let next = characters.get(index + 1).copied();
        if character.is_whitespace() {
            index += 1;
        } else if character == '/' && next == Some('/') {
            while index < characters.len() && characters[index] != '\n' {
                index += 1;
            }
        } else if character == '/' && next == Some('*') {
            index = block_comment_end(&characters, index)?;
        } else if character == '"' {
            index = string_end(&characters, index + 1)?;
        } else if (character == 'r' || character == 'b')
            && let Some(end) = raw_or_byte_literal_end(&characters, index)?
        {
            index = end;
        } else if character == '\'' {
            index = quote_end(&characters, index, &mut tokens);
        } else if character == '_' || character.is_alphabetic() {
            let start = index;
            while index < characters.len()
                && (characters[index] == '_' || characters[index].is_alphanumeric())
            {
                index += 1;
            }
            tokens.push(Token::Identifier(characters[start..index].iter().collect()));
        } else if character.is_ascii_digit() {
            while index < characters.len()
                && (characters[index] == '_' || characters[index].is_alphanumeric())
            {
                index += 1;
            }
        } else {
            tokens.push(Token::Punct(character));
            index += 1;
        }
    }
    Ok(tokens)
}

/// The index after the block comment that starts at `start`; block
/// comments nest.
fn block_comment_end(characters: &[char], start: usize) -> Result<usize, String> {
    let mut depth = 0;
    let mut index = start;
    while index + 1 < characters.len() {
        match (characters[index], characters[index + 1]) {
            ('/', '*') => {
                depth += 1;
                index += 2;
            }
            ('*', '/') => {
                depth -= 1;
                index += 2;
                if depth == 0 {
                    return Ok(index);
                }
            }
            _ => index += 1,
        }
    }
    Err("an unterminated block comment".to_owned())
}

/// The index after the string whose text starts at `start`, after its `"`.
fn string_end(characters: &[char], start: usize) -> Result<usize, String> {
    let mut index = start;
    while index < characters.len() {
        match characters[index] {
            '\\' => index += 2,
            '"' => return Ok(index + 1),
            _ => index += 1,
        }
    }
    Err("an unterminated string".to_owned())
}

/// The index after a raw string, byte string or byte character that starts
/// at `start` with `r` or `b`, or `None` when an identifier starts there.
fn raw_or_byte_literal_end(characters: &[char], start: usize) -> Result<Option<usize>, String> {
    let mut index = start;
    if characters[index] == 'b' {
        index += 1;
        match characters.get(index) {
            Some('"') => return string_end(characters, index + 1).map(Some),
            Some('\'') => return Ok(Some(char_end(characters, index + 1))),
            Some('r') => {}
            _ => return Ok(None),
        }
    }
    // A raw string: `r`, any number of `#`, then `"`.
    index += 1;
    let mut hashes = 0;
    while characters.get(index) == Some(&'#') {
        hashes += 1;
        index += 1;
    }
    if characters.get(index) != Some(&'"') {
        return Ok(None);
    }
    index += 1;
    while index < characters.len() {
        if characters[index] == '"'
            && (1..=hashes).all(|offset| characters.get(index + offset) == Some(&'#'))
        {
            return Ok(Some(index + 1 + hashes));
        }
        index += 1;
    }
    Err("an unterminated raw string".to_owned())
}

/// The index after a character literal whose text starts at `start`, after
/// its `'`.
fn char_end(characters: &[char], start: usize) -> usize {
    let mut index = start;
    if characters.get(index) == Some(&'\\') {
        index += 2;
    } else {
        index += 1;
    }
    while index < characters.len() && characters[index] != '\'' {
        index += 1;
    }
    index + 1
}

/// The index after the `'` at `start`: a character literal is skipped, and a
/// lifetime becomes a `'` and its identifier.
fn quote_end(characters: &[char], start: usize, tokens: &mut Vec<Token>) -> usize {
    let is_literal = matches!(
        (characters.get(start + 1), characters.get(start + 2)),
        (Some('\\'), _) | (Some(_), Some('\''))
    );
    if is_literal {
        char_end(characters, start + 1)
    } else {
        tokens.push(Token::Punct('\''));
        start + 1
    }
}

/// A reader of the tokens of one file.
struct Reader {
    tokens: Vec<Token>,
    index: usize,
}

impl Reader {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.index)
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.index).cloned();
        self.index += 1;
        token
    }

    fn is_punct(&self, punct: char) -> bool {
        self.peek() == Some(&Token::Punct(punct))
    }

    fn is_word(&self, word: &str) -> bool {
        matches!(self.peek(), Some(Token::Identifier(name)) if name == word)
    }

    fn identifier(&mut self) -> Result<String, String> {
        match self.next() {
            Some(Token::Identifier(name)) => Ok(name),
            other => Err(format!("expected a name, found {other:?}")),
        }
    }

    fn expect(&mut self, punct: char) -> Result<(), String> {
        match self.next() {
            Some(Token::Punct(found)) if found == punct => Ok(()),
            other => Err(format!("expected `{punct}`, found {other:?}")),
        }
    }

    /// Skips the group that opens with the current token, `(`, `[` or `{`,
    /// to its closing token, and returns its tokens without the delimiters.
    fn group(&mut self) -> Result<Vec<Token>, String> {
        let mut depth = 0_usize;
        let mut inner = Vec::new();
        loop {
            let token = self.next().ok_or("an unclosed group")?;
            match token {
                Token::Punct('(' | '[' | '{') => {
                    depth += 1;
                    if depth == 1 {
                        continue;
                    }
                }
                Token::Punct(')' | ']' | '}') => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(inner);
                    }
                }
                _ => {}
            }
            inner.push(token);
        }
    }

    /// Skips the rest of an item: to its `;` or to the end of its body, at
    /// the top level of the item.
    fn skip_item(&mut self) -> Result<(), String> {
        loop {
            if self.is_punct('{') {
                self.group()?;
                if self.is_punct(';') {
                    self.next();
                }
                return Ok(());
            }
            if self.is_punct('(') || self.is_punct('[') {
                self.group()?;
                continue;
            }
            match self.next() {
                Some(Token::Punct(';')) => return Ok(()),
                Some(_) => {}
                None => return Err("an item without its end".to_owned()),
            }
        }
    }
}

/// The public names of the crate root that the source of `src/lib.rs`
/// declares.
fn root_names(source: &str) -> Result<BTreeSet<String>, String> {
    let mut reader = Reader {
        tokens: tokens(source)?,
        index: 0,
    };
    let mut names = BTreeSet::new();
    while reader.peek().is_some() {
        let mut exported_macro = false;
        while reader.is_punct('#') {
            reader.next();
            if reader.is_punct('!') {
                reader.next();
            }
            let attribute = reader.group()?;
            exported_macro |= attribute.contains(&Token::Identifier("macro_export".to_owned()));
        }
        if reader.peek().is_none() {
            break;
        }
        if reader.is_word("macro_rules") {
            reader.next();
            reader.expect('!')?;
            let name = reader.identifier()?;
            if exported_macro {
                return Err(format!(
                    "the macro `{name}` is exported into the crate root, which lists no macro"
                ));
            }
            reader.skip_item()?;
            continue;
        }
        if !reader.is_word("pub") {
            reader.skip_item()?;
            continue;
        }
        reader.next();
        if reader.is_punct('(') {
            // A restricted visibility, such as `pub(crate)`: not public.
            reader.group()?;
            reader.skip_item()?;
            continue;
        }
        public_item(&mut reader, &mut names)?;
    }
    Ok(names)
}

/// Reads the public item after its `pub` and adds its names.
fn public_item(reader: &mut Reader, names: &mut BTreeSet<String>) -> Result<(), String> {
    // Qualifiers before the keyword of the item, as in `pub const fn`,
    // `pub unsafe extern "C" fn` and `pub auto trait`; the scan has dropped
    // the string of an ABI.
    while is_qualifier(reader) {
        reader.next();
    }
    let keyword = reader.identifier()?;
    match keyword.as_str() {
        "use" => {
            use_tree(reader, names)?;
            reader.expect(';')
        }
        "extern" => {
            // `pub extern crate name;` or `pub extern crate name as alias;`.
            if reader.identifier()? != "crate" {
                return Err("expected `crate` after `extern`".to_owned());
            }
            let mut name = reader.identifier()?;
            if reader.is_word("as") {
                reader.next();
                name = reader.identifier()?;
            }
            if name != "_" {
                names.insert(name);
            }
            reader.expect(';')
        }
        "mod" | "fn" | "struct" | "enum" | "union" | "trait" | "type" | "const" | "static"
        | "macro" => {
            if keyword == "static" && reader.is_word("mut") {
                reader.next();
            }
            let name = reader.identifier()?;
            if name != "_" {
                names.insert(name);
            }
            reader.skip_item()
        }
        other => Err(format!("an unknown public item `{other}`")),
    }
}

/// Whether the current token qualifies the keyword of an item: `unsafe`,
/// `async`, `safe` and `auto`, and `const` and `extern` when a function or
/// another qualifier follows them, not a name or `crate`.
fn is_qualifier(reader: &Reader) -> bool {
    let Some(Token::Identifier(word)) = reader.peek() else {
        return false;
    };
    match word.as_str() {
        "unsafe" | "async" | "safe" | "auto" => true,
        "const" | "extern" => matches!(
            reader.tokens.get(reader.index + 1),
            Some(Token::Identifier(next)) if ["fn", "unsafe", "async", "extern"].contains(&next.as_str())
        ),
        _ => false,
    }
}

/// Reads one tree of a `use` declaration and adds the names that it brings
/// into scope.
fn use_tree(reader: &mut Reader, names: &mut BTreeSet<String>) -> Result<(), String> {
    if reader.is_punct(':') {
        reader.expect(':')?;
        reader.expect(':')?;
    }
    if reader.is_punct('{') {
        return use_group(reader, names, None);
    }
    if reader.is_punct('*') {
        return Err("a glob re-export, whose names cannot be listed".to_owned());
    }
    let mut last = reader.identifier()?;
    while reader.is_punct(':') {
        reader.expect(':')?;
        reader.expect(':')?;
        if reader.is_punct('{') {
            return use_group(reader, names, Some(last));
        }
        if reader.is_punct('*') {
            return Err("a glob re-export, whose names cannot be listed".to_owned());
        }
        last = reader.identifier()?;
    }
    rename_and_insert(reader, names, last)
}

/// Reads a group `{ ... }` of use trees after the path whose last segment
/// is `parent`, which `self` names.
fn use_group(
    reader: &mut Reader,
    names: &mut BTreeSet<String>,
    parent: Option<String>,
) -> Result<(), String> {
    reader.expect('{')?;
    loop {
        if reader.is_punct('}') {
            reader.next();
            return Ok(());
        }
        if reader.is_word("self") {
            reader.next();
            let parent = parent.clone().ok_or("`self` without a parent path")?;
            rename_and_insert(reader, names, parent)?;
        } else {
            use_tree(reader, names)?;
        }
        if reader.is_punct(',') {
            reader.next();
        }
    }
}

/// Adds `name`, or the name after a following `as`, unless it is `_`.
fn rename_and_insert(
    reader: &mut Reader,
    names: &mut BTreeSet<String>,
    name: String,
) -> Result<(), String> {
    let name = if reader.is_word("as") {
        reader.next();
        reader.identifier()?
    } else {
        name
    };
    if name != "_" {
        names.insert(name);
    }
    Ok(())
}

/// The names of the list: one per line, in byte order and without
/// repetitions, each a Rust identifier.
fn listed_names(list: &str) -> Result<Vec<String>, String> {
    let mut names: Vec<String> = Vec::new();
    for (index, line) in list.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let valid = line.starts_with(|c: char| c == '_' || c.is_ascii_alphabetic())
            && line.chars().all(|c| c == '_' || c.is_ascii_alphanumeric());
        if !valid {
            return Err(format!("line {}: `{line}` is not a name", index + 1));
        }
        if let Some(last) = names.last()
            && last.as_str() >= line
        {
            return Err(format!(
                "line {}: `{line}` is not after `{last}` in byte order",
                index + 1
            ));
        }
        names.push(line.to_owned());
    }
    Ok(names)
}

/// Compares the public names of the crate root in `source` with `list`, and
/// names every difference.
fn compare(source: &str, list: &str) -> Result<(), String> {
    let found = root_names(source)?;
    let listed: BTreeSet<String> = listed_names(list)?.into_iter().collect();
    let unlisted: Vec<&String> = found.difference(&listed).collect();
    let missing: Vec<&String> = listed.difference(&found).collect();
    if unlisted.is_empty() && missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "public in the crate root but not in api/root-names.txt: {unlisted:?}; listed but not public: {missing:?}"
        ))
    }
}

// The crate root has exactly the public names of the list.
#[test]
fn the_crate_root_has_exactly_the_listed_public_names() {
    compare(LIB, LIST).unwrap();
    assert_eq!(root_names(LIB).unwrap().len(), 28);
}

// A public name added to the crate root without the list changing fails the
// comparison, and so does a name removed from it.
#[test]
fn a_public_name_added_without_the_list_changing_fails() {
    for addition in [
        "pub use command::Settings;",
        "pub use command::serialize as write_line;",
        "pub use context::{Storage, CancelFlag};",
        "pub fn version() -> u32 { 1 }",
        "pub mod extra;",
        "pub const LIMITS: Limits = Limits::new();",
    ] {
        let source = format!("{LIB}\n{addition}\n");
        let error = compare(&source, LIST).unwrap_err();
        assert!(
            error.contains("public in the crate root but not in"),
            "{addition}: {error}"
        );
        assert!(error.ends_with("listed but not public: []"), "{error}");
    }
    let source = format!("{LIB}\npub use command::Settings;\n");
    let error = compare(&source, LIST).unwrap_err();
    assert!(
        error.contains("not in api/root-names.txt: [\"Settings\"];"),
        "{error}"
    );
    let source = LIB.replace(
        "pub use command::{Outcome, Request, execute};",
        "pub use command::{Outcome, execute};",
    );
    assert_ne!(source, LIB);
    let error = compare(&source, LIST).unwrap_err();
    assert!(
        error.ends_with("listed but not public: [\"Request\"]"),
        "{error}"
    );
}

// A macro exported with `#[macro_export]` from any module lands in the crate
// root, which lists no macro: no Rust file under `src/` exports one.
#[test]
fn no_file_under_src_exports_a_macro() {
    let export = Token::Identifier("macro_export".to_owned());
    let mut files = 0;
    let mut stack = vec![PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/src"))];
    while let Some(directory) = stack.pop() {
        for entry in fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                let source = fs::read_to_string(&path).unwrap();
                assert!(
                    !tokens(&source).unwrap().contains(&export),
                    "{} exports a macro into the crate root",
                    path.display()
                );
                files += 1;
            }
        }
    }
    assert!(files > 1, "the scan reads the files under src/: {files}");
    let exported = "mod inner {\n    #[macro_export]\n    macro_rules! shown { () => {}; }\n}\n";
    assert!(tokens(exported).unwrap().contains(&export));
}

// The scan reads every form of public item and of `use` tree, renamings
// included, and skips private and restricted items, comments, literals,
// attributes and item bodies; a glob re-export and an exported macro fail
// the scan.
#[test]
fn the_scan_reads_every_form_of_public_item() {
    let source = r##"
//! pub fn in_a_comment() {}
/* pub mod in_a_block /* nested */ comment; */
#![forbid(unsafe_code)]
const _: () = assert!(true, "pub fn in_a_string() {}");
const RAW: &str = r#"pub fn in_a_raw_string() {}"#;
pub mod one;
pub(crate) mod hidden;
mod private;
#[doc = "pub fn in_an_attribute"]
pub use path::{Two, three::Four as Five, six::{self as Seven, Eight}, _unused as _};
pub use ::absolute::Nine;
pub use path::Ten as Eleven;
pub use {path::TwentyOne, other::TwentyTwo as TwentyThree};
pub fn twelve<'a>(x: &'a str) -> char { let _ = 'c'; 'd' }
pub const fn thirteen() {}
pub unsafe fn fourteen() {}
pub struct Fifteen { pub field: u8 }
pub enum Sixteen { A, B }
pub trait Seventeen { fn method(&self); }
pub type Eighteen = u8;
pub const NINETEEN: u8 = b'x';
pub static TWENTY: &[u8] = b"pub fn in_bytes";
pub const _: () = ();
impl Fifteen { pub fn method(&self) {} }
pub(in crate::one) fn restricted() {}
macro_rules! private_macro { () => {}; }
"##;
    let names: Vec<String> = root_names(source).unwrap().into_iter().collect();
    assert_eq!(
        names,
        [
            "Eight",
            "Eighteen",
            "Eleven",
            "Fifteen",
            "Five",
            "NINETEEN",
            "Nine",
            "Seven",
            "Seventeen",
            "Sixteen",
            "TWENTY",
            "TwentyOne",
            "TwentyThree",
            "Two",
            "fourteen",
            "one",
            "thirteen",
            "twelve",
        ]
    );
    assert!(root_names("pub use path::*;").unwrap_err().contains("glob"));
    assert!(
        root_names("pub use path::{a, b::*};")
            .unwrap_err()
            .contains("glob")
    );
    let exported = "#[macro_export]\nmacro_rules! shown { () => {}; }\n";
    assert!(root_names(exported).unwrap_err().contains("exported"));
}

// The list holds names in byte order without repetitions.
#[test]
fn the_list_holds_names_in_byte_order() {
    assert!(listed_names("# A comment.\n\nA\nB\na\n").is_ok());
    assert!(listed_names("b\na\n").unwrap_err().contains("byte order"));
    assert!(listed_names("a\na\n").unwrap_err().contains("byte order"));
    assert!(listed_names("a b\n").unwrap_err().contains("not a name"));
    assert!(listed_names("1a\n").unwrap_err().contains("not a name"));
}
