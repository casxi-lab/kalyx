//! The names of symbols.
//!
//! A symbol name is an ASCII letter or `_`, followed by ASCII letters,
//! digits and `_`: the identifiers of the input syntax. The names `pi`, `i`
//! and `undefined` are reserved for constants of a later release, so that an
//! input accepted today keeps its meaning and its canonical form when the
//! constants arrive. The parser reads identifiers and rejects the reserved
//! names with the same functions, so the two rules cannot drift apart.

use crate::{Error, FaultKind, Result, Span};

/// Checks that `name` is a symbol name that is not reserved; charges nothing
/// and reads each byte of the name at most once for the form and once for
/// the reserved names.
///
/// # Errors
///
/// `Fault(Syntax)` with the span of the first character that a name does not
/// allow, or an empty span at 0 for the empty name; `Fault(Unsupported)` with
/// the span of the whole name for a reserved name.
pub(super) fn check_name(name: &str) -> Result<()> {
    match invalid_span(name.as_bytes()) {
        Some(span) => Err(Error::new(
            FaultKind::Syntax,
            Some(span),
            "a symbol name is a letter or `_` followed by letters, digits and `_`",
        )),
        None => {
            if is_reserved(name.as_bytes()) {
                Err(Error::new(
                    FaultKind::Unsupported,
                    Span::new(0, name.len()),
                    "the name is reserved for a constant",
                ))
            } else {
                Ok(())
            }
        }
    }
}

/// The span of the first character of `name` that a symbol name does not
/// allow, an empty span at 0 for the empty name, or `None` for a valid name.
fn invalid_span(name: &[u8]) -> Option<Span> {
    if name.is_empty() {
        return Span::new(0, 0);
    }
    first_invalid(name)
}

/// The span of the first character of the nonempty `name` that a symbol name
/// does not allow, or `None`.
fn first_invalid(name: &[u8]) -> Option<Span> {
    let mut index = 0;
    while index < name.len() {
        let byte = name[index];
        let allowed = if index == 0 {
            starts_name(byte)
        } else {
            continues_name(byte)
        };
        if !allowed {
            // Every byte before is ASCII, so `index` starts a character.
            return Span::new(index, index + character_length(byte));
        }
        index += 1;
    }
    None
}

/// Whether `byte` starts a symbol name: an ASCII letter or `_`.
pub(crate) const fn starts_name(byte: u8) -> bool {
    is_letter(byte) || byte == b'_'
}

/// Whether `byte` continues a symbol name: an ASCII letter, an ASCII digit
/// or `_`.
pub(crate) const fn continues_name(byte: u8) -> bool {
    is_letter(byte) || is_digit(byte) || byte == b'_'
}

/// Whether `byte` is an ASCII letter.
const fn is_letter(byte: u8) -> bool {
    (byte >= b'a' && byte <= b'z') || (byte >= b'A' && byte <= b'Z')
}

/// Whether `byte` is an ASCII digit.
pub(crate) const fn is_digit(byte: u8) -> bool {
    byte >= b'0' && byte <= b'9'
}

/// The length in bytes of the UTF-8 character that starts with `byte`.
pub(crate) const fn character_length(byte: u8) -> usize {
    if byte < 0x80 {
        1
    } else if byte >= 0xF0 {
        4
    } else if byte >= 0xE0 {
        3
    } else {
        2
    }
}

/// Whether `name` is reserved for a constant of a later release: `pi`, `i`
/// or `undefined`.
pub(crate) fn is_reserved(name: &[u8]) -> bool {
    same_bytes(name, b"pi") || same_bytes(name, b"i") || same_bytes(name, b"undefined")
}

/// Whether two byte strings are equal.
fn same_bytes(left: &[u8], right: &[u8]) -> bool {
    let mut index = 0;
    while index < left.len() && index < right.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    left.len() == right.len()
}
