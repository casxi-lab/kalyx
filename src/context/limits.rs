//! The limits of a request: nine fields, each with a default.

use crate::LimitField;

/// The limits of one request.
///
/// Every field bounds exactly one quantity and has a default; start from
/// [`Limits::new`] or [`Limits::default`], which give the same values, and
/// change single fields with the `with_<field>` methods. A value is applied as
/// it is given: no code bounds a field by a constant, by another field or by a
/// machine width that no field names. Each field corresponds to one variant of
/// [`LimitField`], which names it when it is exceeded.
///
/// ```
/// use kalyx::{LimitField, Limits};
///
/// let limits = Limits::new().with_max_work(1_000_000).with_max_frames(100);
/// assert_eq!(limits.max_work, 1_000_000);
/// assert_eq!(limits.get(LimitField::Frames), 100);
/// assert_eq!(Limits::default().max_depth, 128);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Limits {
    /// The work units that the request may charge. Default 100000.
    pub max_work: u64,
    /// The bytes of the request's input; with a nonempty operand table, of
    /// all its text operands together. Default 65536.
    pub max_input_bytes: u64,
    /// The bytes of all display and serialization of the request,
    /// cumulative. Default 65536, no larger than the default `max_work`, so
    /// that under the default limits output reaches this field before the
    /// work, which each output byte also charges.
    pub max_output_bytes: u64,
    /// The nesting depth of syntax, terms and values. Default 128.
    pub max_depth: u64,
    /// The nodes retained at one time: the costs of the open frames, the
    /// reserved temporaries and the value being admitted. The size of one
    /// value is a special case of this total. Default 8192.
    pub max_nodes: u64,
    /// The logical storage bytes retained at one time, over the same parts as
    /// `max_nodes`, each measured by the byte formula of its value kind.
    /// Default 262144.
    pub max_storage_bytes: u64,
    /// The bits of one integer. Default 4096.
    pub max_integer_bits: u64,
    /// The absolute value of one integer exponent; also degrees and orders of
    /// derivatives. Default 4096.
    pub max_exponent: u64,
    /// The frames open at one time. Default 32.
    pub max_frames: u64,
}

impl Limits {
    /// The default limits.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max_work: 100_000,
            max_input_bytes: 65_536,
            max_output_bytes: 65_536,
            max_depth: 128,
            max_nodes: 8_192,
            max_storage_bytes: 262_144,
            max_integer_bits: 4_096,
            max_exponent: 4_096,
            max_frames: 32,
        }
    }

    /// These limits with `max_work` set to `value`.
    #[must_use]
    pub const fn with_max_work(mut self, value: u64) -> Self {
        self.max_work = value;
        self
    }

    /// These limits with `max_input_bytes` set to `value`.
    #[must_use]
    pub const fn with_max_input_bytes(mut self, value: u64) -> Self {
        self.max_input_bytes = value;
        self
    }

    /// These limits with `max_output_bytes` set to `value`.
    #[must_use]
    pub const fn with_max_output_bytes(mut self, value: u64) -> Self {
        self.max_output_bytes = value;
        self
    }

    /// These limits with `max_depth` set to `value`.
    #[must_use]
    pub const fn with_max_depth(mut self, value: u64) -> Self {
        self.max_depth = value;
        self
    }

    /// These limits with `max_nodes` set to `value`.
    #[must_use]
    pub const fn with_max_nodes(mut self, value: u64) -> Self {
        self.max_nodes = value;
        self
    }

    /// These limits with `max_storage_bytes` set to `value`.
    #[must_use]
    pub const fn with_max_storage_bytes(mut self, value: u64) -> Self {
        self.max_storage_bytes = value;
        self
    }

    /// These limits with `max_integer_bits` set to `value`.
    #[must_use]
    pub const fn with_max_integer_bits(mut self, value: u64) -> Self {
        self.max_integer_bits = value;
        self
    }

    /// These limits with `max_exponent` set to `value`.
    #[must_use]
    pub const fn with_max_exponent(mut self, value: u64) -> Self {
        self.max_exponent = value;
        self
    }

    /// These limits with `max_frames` set to `value`.
    #[must_use]
    pub const fn with_max_frames(mut self, value: u64) -> Self {
        self.max_frames = value;
        self
    }

    /// The value of the field that `field` names.
    #[must_use]
    pub const fn get(&self, field: LimitField) -> u64 {
        match field {
            LimitField::Work => self.max_work,
            LimitField::InputBytes => self.max_input_bytes,
            LimitField::OutputBytes => self.max_output_bytes,
            LimitField::Depth => self.max_depth,
            LimitField::Nodes => self.max_nodes,
            LimitField::StorageBytes => self.max_storage_bytes,
            LimitField::IntegerBits => self.max_integer_bits,
            LimitField::Exponent => self.max_exponent,
            LimitField::Frames => self.max_frames,
        }
    }
}

impl Default for Limits {
    /// The default limits, the same as [`Limits::new`].
    fn default() -> Self {
        Self::new()
    }
}

/// The number of fields of `Limits`. The pattern names every field and has no
/// `..`, so adding a field fails to compile here until this count changes
/// with it.
const FIELDS: usize = {
    let Limits {
        max_work: _,
        max_input_bytes: _,
        max_output_bytes: _,
        max_depth: _,
        max_nodes: _,
        max_storage_bytes: _,
        max_integer_bits: _,
        max_exponent: _,
        max_frames: _,
    } = Limits::new();
    9
};

// `LimitField` has one variant for each field, and there are at most ten
// fields: a new limit is a new field with a default and a new variant.
const _: () = assert!(
    LimitField::ALL.len() == FIELDS,
    "LimitField has one variant per field of Limits"
);
const _: () = assert!(FIELDS <= 10, "Limits has at most ten fields");
