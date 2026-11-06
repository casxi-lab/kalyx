//! The source scan of the guard step: what the non-test code of one Rust
//! source file of the kalyx package uses.
//!
//! # Non-test code
//!
//! The file is parsed with `syn`, so comments, documentation comments and
//! string literals are never read as code. Test code is skipped: an item,
//! module, associated item, `let` statement or macro statement whose
//! attributes include `#[test]`, or a `#[cfg(...)]` whose predicate implies
//! `test` (`test`, an `all(...)` with such a member, or an `any(...)` whose
//! members all imply it). A `#[cfg(test)]` on an expression, a field, a
//! variant or a match arm does not exempt it. A module declared as
//! `#[cfg(test)] mod name;` is reported in [`Scanned::test_modules`] and one
//! declared as non-test code in [`Scanned::modules`], so that the caller
//! skips the file of a module that only test code declares.
//!
//! The bodies of macro invocations and definitions, the arguments of
//! attributes and syntax that `syn` keeps as raw tokens are scanned token by
//! token with the same rules.
//!
//! # Rules
//!
//! Non-test code must not contain:
//!
//! - a path below `std::thread`, or an identifier named in [`NAMES`]
//!   (`HashMap`, `HashSet`, `RandomState`, `SystemTime`, `thread_local`,
//!   `catch_unwind`), or a `static mut` item;
//! - a method call `.name(` or a path `f32::name` or `f64::name` (also
//!   `<f64>::name`), where `name` is one of the transcendental functions in
//!   [`LIBM`]. The scan sees names, not types: a call through a type alias,
//!   a generic parameter or a trait such as `Float` is left to Clippy, whose
//!   `disallowed-methods` in `clippy.toml` resolve the type;
//! - outside `src/main.rs`, `src/command.rs` and `src/command/`, a path
//!   `Context::name` or `<Context as Trait>::name` with any `name`, a struct
//!   expression `Context { .. }`, an import that renames `Context` or a type
//!   alias of it. A value built as `Self` inside the impl blocks of the type,
//!   through an inferred `Default::default()` or through a conversion such
//!   as `From` is not seen;
//! - a path that starts with `std`, in a `use` declaration, an expression, a
//!   type, a pattern, a macro or an attribute, that the std allow list does
//!   not permit. A `use` tree is expanded first, so `use std::{io, fmt};`
//!   names the paths `std::io` and `std::fmt`, and a glob `use std::fmt::*;`
//!   names `std::fmt`. `extern crate std as name;` names the path `std`.

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use syn::punctuated::Punctuated;
use syn::visit::{self, Visit};
use syn::{
    Attribute, Expr, ForeignItem, ImplItem, Item, Meta, Pat, Path, StaticMutability, Stmt,
    TraitItem, Type, TypeParamBound, UseTree,
};

use crate::guard;

/// The identifiers that non-test code must not use, with how a finding
/// shows them.
pub const NAMES: [(&str, &str); 6] = [
    ("HashMap", "HashMap"),
    ("HashSet", "HashSet"),
    ("RandomState", "RandomState"),
    ("SystemTime", "SystemTime"),
    ("thread_local", "thread_local!"),
    ("catch_unwind", "catch_unwind"),
];

/// The transcendental functions of the platform math library, as methods
/// of `f32` and `f64`.
pub const LIBM: [&str; 25] = [
    "sin", "cos", "tan", "sin_cos", "asin", "acos", "atan", "atan2", "sinh", "cosh", "tanh",
    "asinh", "acosh", "atanh", "exp", "exp2", "exp_m1", "ln", "log", "log2", "log10", "ln_1p",
    "powf", "cbrt", "hypot",
];

/// The type that only the command entry and the program may construct.
/// Every associated function or constant reached through its name counts
/// as constructing it.
pub const CONTEXT: &str = "Context";

/// A finding: the line and what was found there.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Finding {
    pub line: usize,
    pub message: String,
}

/// What the scan of one file found.
#[derive(Debug, Default)]
pub struct Scanned {
    pub findings: Vec<Finding>,
    /// The modules declared as test code with `mod name;`, as
    /// repository-relative paths without the extension: the module `p` is
    /// the file `p.rs` or `p/mod.rs`, and its submodules are below `p/`.
    pub test_modules: Vec<String>,
    /// The modules declared as non-test code with `mod name;`, in the same
    /// form.
    pub modules: Vec<String>,
}

/// Whether `path` may construct [`CONTEXT`]: the program and the command
/// entry.
pub fn may_construct_context(path: &str) -> bool {
    path == "src/main.rs" || path == "src/command.rs" || path.starts_with("src/command/")
}

/// Scans the source file at the repository-relative `path` with content
/// `text`. `std_allowed` tells whether the std allow list permits a path
/// such as `std::io::stdin`. Fails when the file cannot be parsed.
pub fn scan(
    path: &str,
    text: &str,
    std_allowed: &dyn Fn(&str) -> bool,
) -> Result<Scanned, Finding> {
    let file = syn::parse_file(text).map_err(|error| Finding {
        line: line(error.span()),
        message: format!("cannot parse: {error}"),
    })?;
    let mut scanner = Scanner {
        std_allowed,
        context_allowed: may_construct_context(path),
        module_dir: module_dir(path),
        inline: Vec::new(),
        moved: 0,
        scanned: Scanned::default(),
    };
    scanner.visit_file(&file);
    let mut scanned = scanner.scanned;
    scanned.findings.sort();
    scanned.findings.dedup();
    Ok(scanned)
}

/// The directory that holds the files of the modules that `path` declares:
/// the directory of a crate root or `mod.rs` file, and otherwise the path
/// without its `.rs` extension.
fn module_dir(path: &str) -> String {
    let (dir, file) = path.rsplit_once('/').unwrap_or(("", path));
    if matches!(file, "lib.rs" | "main.rs" | "mod.rs") || dir == "src/bin" || path == "build.rs" {
        dir.to_string()
    } else {
        path.strip_suffix(".rs").unwrap_or(path).to_string()
    }
}

/// The line, counted from 1, where `span` starts.
fn line(span: Span) -> usize {
    span.start().line
}

/// An identifier as written, without the `r#` of a raw identifier.
fn plain(ident: &proc_macro2::Ident) -> String {
    let text = ident.to_string();
    match text.strip_prefix("r#") {
        Some(rest) => rest.to_string(),
        None => text,
    }
}

/// Whether `attrs` mark test code: `#[test]`, or a `#[cfg(...)]` whose
/// predicate implies `test`.
fn is_test_code(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        if path.is_ident("test") {
            return true;
        }
        path.is_ident("cfg")
            && attr
                .parse_args::<Meta>()
                .is_ok_and(|meta| implies_test(&meta))
    })
}

/// Whether the configuration predicate `meta` can hold only in a test
/// build.
fn implies_test(meta: &Meta) -> bool {
    match meta {
        Meta::Path(path) => path.is_ident("test"),
        Meta::List(list) => {
            let Ok(members) =
                list.parse_args_with(Punctuated::<Meta, syn::Token![,]>::parse_terminated)
            else {
                return false;
            };
            if list.path.is_ident("all") {
                members.iter().any(implies_test)
            } else if list.path.is_ident("any") {
                !members.is_empty() && members.iter().all(implies_test)
            } else {
                false
            }
        }
        Meta::NameValue(_) => false,
    }
}

fn item_attrs(item: &Item) -> &[Attribute] {
    match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::ExternCrate(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::ForeignMod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::TraitAlias(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Use(item) => &item.attrs,
        _ => &[],
    }
}

fn impl_item_attrs(item: &ImplItem) -> &[Attribute] {
    match item {
        ImplItem::Const(item) => &item.attrs,
        ImplItem::Fn(item) => &item.attrs,
        ImplItem::Type(item) => &item.attrs,
        ImplItem::Macro(item) => &item.attrs,
        _ => &[],
    }
}

fn trait_item_attrs(item: &TraitItem) -> &[Attribute] {
    match item {
        TraitItem::Const(item) => &item.attrs,
        TraitItem::Fn(item) => &item.attrs,
        TraitItem::Type(item) => &item.attrs,
        TraitItem::Macro(item) => &item.attrs,
        _ => &[],
    }
}

fn foreign_item_attrs(item: &ForeignItem) -> &[Attribute] {
    match item {
        ForeignItem::Fn(item) => &item.attrs,
        ForeignItem::Static(item) => &item.attrs,
        ForeignItem::Type(item) => &item.attrs,
        ForeignItem::Macro(item) => &item.attrs,
        _ => &[],
    }
}

/// Whether `attrs` hold a `#[path = ...]` attribute, which moves a module
/// file away from its usual place.
fn has_path_attr(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path().is_ident("path"))
}

/// The segments of `path`, without a leading `::`, and the line where it
/// starts.
fn segments(path: &Path) -> (Vec<String>, usize) {
    let names = path
        .segments
        .iter()
        .map(|segment| plain(&segment.ident))
        .collect();
    let at = path
        .segments
        .first()
        .map_or(0, |segment| line(segment.ident.span()));
    (names, at)
}

/// The paths that a `use` tree names, each with the line of its last
/// segment. A glob names the path of its parent module.
fn use_paths(prefix: &mut Vec<String>, tree: &UseTree, out: &mut Vec<(Vec<String>, usize)>) {
    match tree {
        UseTree::Path(path) => {
            prefix.push(plain(&path.ident));
            use_paths(prefix, &path.tree, out);
            prefix.pop();
        }
        UseTree::Name(name) => {
            let mut full = prefix.clone();
            if name.ident != "self" {
                full.push(plain(&name.ident));
            }
            out.push((full, line(name.ident.span())));
        }
        UseTree::Rename(rename) => {
            let mut full = prefix.clone();
            if rename.ident != "self" {
                full.push(plain(&rename.ident));
            }
            out.push((full, line(rename.ident.span())));
        }
        UseTree::Glob(glob) => out.push((prefix.clone(), line(glob.star_token.span))),
        UseTree::Group(group) => {
            for tree in &group.items {
                use_paths(prefix, tree, out);
            }
        }
    }
}

/// Whether the type `ty` is a path to a type named [`CONTEXT`].
fn aliases_context(ty: &Type) -> bool {
    match ty {
        Type::Path(ty) => ty
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == CONTEXT),
        Type::Paren(inner) => aliases_context(&inner.elem),
        Type::Group(inner) => aliases_context(&inner.elem),
        _ => false,
    }
}

struct Scanner<'a> {
    std_allowed: &'a dyn Fn(&str) -> bool,
    context_allowed: bool,
    /// The directory of the modules that the file declares at its top
    /// level.
    module_dir: String,
    /// The inline modules around the current item.
    inline: Vec<String>,
    /// How many of the inline modules around the current item have a
    /// `#[path]` attribute; test module files are not resolved below one.
    moved: usize,
    scanned: Scanned,
}

impl Scanner<'_> {
    fn find(&mut self, line: usize, message: String) {
        self.scanned.findings.push(Finding { line, message });
    }

    fn check_name(&mut self, name: &str, at: usize) {
        if let Some((_, shown)) = NAMES.iter().find(|(denied, _)| *denied == name) {
            self.find(at, format!("`{shown}` is not allowed in non-test code"));
        }
    }

    /// The rules for a path that starts at the crate root of `std` or
    /// elsewhere; only `std` paths are checked.
    fn check_std(&mut self, segments: &[String], at: usize) {
        if segments.first().is_none_or(|first| first != "std") {
            return;
        }
        let full = segments.join("::");
        if segments.get(1).is_some_and(|second| second == "thread") {
            self.find(
                at,
                format!("`std::thread` is not allowed in non-test code (`{full}`)"),
            );
        }
        if !(self.std_allowed)(&full) {
            self.find(
                at,
                format!("std path `{full}` is not in {}", guard::STD_PATHS),
            );
        }
    }

    /// The rules for a pair of adjacent path segments.
    fn check_pair(&mut self, first: &str, second: &str, at: usize) {
        if matches!(first, "f32" | "f64") && LIBM.contains(&second) {
            self.find(
                at,
                format!(
                    "`{first}::{second}` is a transcendental function of the platform math library"
                ),
            );
        }
        if first == CONTEXT {
            self.context(at);
        }
    }

    fn context_alias(&mut self, at: usize) {
        if !self.context_allowed {
            self.find(
                at,
                format!(
                    "`{CONTEXT}` is renamed or aliased outside src/main.rs, src/command.rs and src/command/"
                ),
            );
        }
    }

    /// The repository-relative path, without the extension, of the module
    /// `name` declared with `mod name;` in the current inline modules.
    fn module_path(&self, name: &proc_macro2::Ident) -> String {
        let mut path = self.module_dir.clone();
        for segment in self.inline.iter().chain([&plain(name)]) {
            if !path.is_empty() {
                path.push('/');
            }
            path.push_str(segment);
        }
        path
    }

    /// Whether a module file declared here is at its usual place: no
    /// `#[path]` on it or on an inline module around it.
    fn usual_place(&self, attrs: &[Attribute]) -> bool {
        self.moved == 0 && !has_path_attr(attrs)
    }

    fn context(&mut self, at: usize) {
        if !self.context_allowed {
            self.find(
                at,
                format!(
                    "`{CONTEXT}` is constructed outside src/main.rs, src/command.rs and src/command/"
                ),
            );
        }
    }

    fn method(&mut self, name: &str, at: usize) {
        if LIBM.contains(&name) {
            self.find(
                at,
                format!(".{name}( calls a transcendental function of the platform math library"),
            );
        }
    }

    /// Scans raw tokens, such as the body of a macro.
    fn scan_tokens(&mut self, tokens: &TokenStream) {
        let tokens: Vec<TokenTree> = tokens.clone().into_iter().collect();
        let punct = |at: usize, c: char| matches!(tokens.get(at), Some(TokenTree::Punct(punct)) if punct.as_char() == c);
        let ident = |at: usize| match tokens.get(at) {
            Some(TokenTree::Ident(ident)) => Some(plain(ident)),
            _ => None,
        };
        let colons = |at: usize| punct(at, ':') && punct(at + 1, ':');
        for (at, token) in tokens.iter().enumerate() {
            match token {
                TokenTree::Group(group) => self.scan_tokens(&group.stream()),
                TokenTree::Punct(punct_token) if punct_token.as_char() == '.' => {
                    let calls = matches!(
                        tokens.get(at + 2),
                        Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Parenthesis
                    );
                    if let Some(name) =
                        ident(at + 1).filter(|_| calls && !punct(at.wrapping_sub(1), '.'))
                    {
                        self.method(&name, line(token.span()));
                    }
                }
                TokenTree::Ident(word) => {
                    let name = plain(word);
                    let at_line = line(word.span());
                    self.check_name(&name, at_line);
                    if name == "static" && ident(at + 1).as_deref() == Some("mut") {
                        self.find(
                            at_line,
                            "`static mut` is not allowed in non-test code".into(),
                        );
                    }
                    if colons(at + 1)
                        && let Some(next) = ident(at + 3)
                    {
                        self.check_pair(&name, &next, at_line);
                    }
                    if name == CONTEXT
                        && matches!(
                            tokens.get(at + 1),
                            Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Brace
                        )
                    {
                        let declares = at.checked_sub(1).and_then(ident).is_some_and(|before| {
                            matches!(
                                before.as_str(),
                                "struct" | "enum" | "union" | "impl" | "for" | "trait" | "mod"
                            )
                        }) || (punct(at.wrapping_sub(1), '>')
                            && punct(at.wrapping_sub(2), '-'));
                        if !declares {
                            self.context(at_line);
                        }
                    }
                    // A path that starts at `std`, with or without a leading
                    // `::`, but not a segment `std` inside another path.
                    let nested = at >= 3 && colons(at - 2) && ident(at - 3).is_some();
                    if name == "std" && !nested {
                        let mut path = vec![name];
                        let mut next = at + 1;
                        while colons(next) {
                            let Some(segment) = ident(next + 2) else {
                                break;
                            };
                            path.push(segment);
                            next += 3;
                        }
                        self.check_std(&path, at_line);
                    }
                }
                _ => {}
            }
        }
    }
}

impl<'ast> Visit<'ast> for Scanner<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        if is_test_code(item_attrs(item)) {
            if let Item::Mod(module) = item
                && module.content.is_none()
                && self.usual_place(&module.attrs)
            {
                let path = self.module_path(&module.ident);
                self.scanned.test_modules.push(path);
            }
            return;
        }
        match item {
            Item::Verbatim(tokens) => self.scan_tokens(tokens),
            Item::ExternCrate(krate) if krate.ident == "std" && krate.rename.is_some() => {
                self.check_std(&["std".to_string()], line(krate.ident.span()));
                visit::visit_item(self, item);
            }
            _ => visit::visit_item(self, item),
        }
    }

    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        if module.content.is_none() {
            if self.usual_place(&module.attrs) {
                let path = self.module_path(&module.ident);
                self.scanned.modules.push(path);
            }
            visit::visit_item_mod(self, module);
            return;
        }
        let moved = has_path_attr(&module.attrs);
        self.inline.push(plain(&module.ident));
        self.moved += usize::from(moved);
        visit::visit_item_mod(self, module);
        self.moved -= usize::from(moved);
        self.inline.pop();
    }

    fn visit_impl_item(&mut self, item: &'ast ImplItem) {
        match item {
            _ if is_test_code(impl_item_attrs(item)) => {}
            ImplItem::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_impl_item(self, item),
        }
    }

    fn visit_trait_item(&mut self, item: &'ast TraitItem) {
        match item {
            _ if is_test_code(trait_item_attrs(item)) => {}
            TraitItem::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_trait_item(self, item),
        }
    }

    fn visit_foreign_item(&mut self, item: &'ast ForeignItem) {
        match item {
            _ if is_test_code(foreign_item_attrs(item)) => {}
            ForeignItem::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_foreign_item(self, item),
        }
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        match stmt {
            Stmt::Local(local) if is_test_code(&local.attrs) => {}
            Stmt::Macro(mac) if is_test_code(&mac.attrs) => {}
            _ => visit::visit_stmt(self, stmt),
        }
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        match expr {
            Expr::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_expr(self, expr),
        }
    }

    fn visit_type(&mut self, ty: &'ast Type) {
        match ty {
            Type::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_type(self, ty),
        }
    }

    fn visit_pat(&mut self, pat: &'ast Pat) {
        match pat {
            Pat::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_pat(self, pat),
        }
    }

    fn visit_type_param_bound(&mut self, bound: &'ast TypeParamBound) {
        match bound {
            TypeParamBound::Verbatim(tokens) => self.scan_tokens(tokens),
            _ => visit::visit_type_param_bound(self, bound),
        }
    }

    fn visit_ident(&mut self, ident: &'ast proc_macro2::Ident) {
        self.check_name(&plain(ident), line(ident.span()));
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        if let StaticMutability::Mut(token) = &item.mutability {
            self.find(
                line(token.span),
                "`static mut` is not allowed in non-test code".into(),
            );
        }
        visit::visit_item_static(self, item);
    }

    fn visit_foreign_item_static(&mut self, item: &'ast syn::ForeignItemStatic) {
        if let StaticMutability::Mut(token) = &item.mutability {
            self.find(
                line(token.span),
                "`static mut` is not allowed in non-test code".into(),
            );
        }
        visit::visit_foreign_item_static(self, item);
    }

    fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
        self.method(&plain(&call.method), line(call.method.span()));
        visit::visit_expr_method_call(self, call);
    }

    fn visit_path(&mut self, path: &'ast Path) {
        let (names, at) = segments(path);
        self.check_std(&names, at);
        for (pair, segment) in names.windows(2).zip(path.segments.iter().skip(1)) {
            self.check_pair(&pair[0], &pair[1], line(segment.ident.span()));
        }
        visit::visit_path(self, path);
    }

    fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
        if let (Some(qself), Some(last)) = (&expr.qself, expr.path.segments.last())
            && let Type::Path(ty) = qself.ty.as_ref()
            && let Some(own) = ty.path.segments.last()
        {
            self.check_pair(
                &plain(&own.ident),
                &plain(&last.ident),
                line(last.ident.span()),
            );
        }
        visit::visit_expr_path(self, expr);
    }

    fn visit_expr_struct(&mut self, expr: &'ast syn::ExprStruct) {
        if let Some(last) = expr.path.segments.last()
            && last.ident == CONTEXT
        {
            self.context(line(last.ident.span()));
        }
        visit::visit_expr_struct(self, expr);
    }

    fn visit_use_rename(&mut self, rename: &'ast syn::UseRename) {
        if rename.ident == CONTEXT && rename.rename != CONTEXT && rename.rename != "_" {
            self.context_alias(line(rename.rename.span()));
        }
        visit::visit_use_rename(self, rename);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        if item.ident != CONTEXT && aliases_context(&item.ty) {
            self.context_alias(line(item.ident.span()));
        }
        visit::visit_item_type(self, item);
    }

    fn visit_impl_item_type(&mut self, item: &'ast syn::ImplItemType) {
        if item.ident != CONTEXT && aliases_context(&item.ty) {
            self.context_alias(line(item.ident.span()));
        }
        visit::visit_impl_item_type(self, item);
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        let mut paths = Vec::new();
        use_paths(&mut Vec::new(), &item.tree, &mut paths);
        for (path, at) in paths {
            self.check_std(&path, at);
        }
        visit::visit_item_use(self, item);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        self.scan_tokens(&mac.tokens);
        visit::visit_macro(self, mac);
    }

    fn visit_meta_list(&mut self, list: &'ast syn::MetaList) {
        self.scan_tokens(&list.tokens);
        visit::visit_meta_list(self, list);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The findings in `text` at `path`, as `line: message`, with every
    /// `std` path permitted.
    fn findings_at(path: &str, text: &str) -> Vec<String> {
        let scanned = scan(path, text, &|_| true).expect("the source parses");
        scanned
            .findings
            .iter()
            .map(|finding| format!("{}: {}", finding.line, finding.message))
            .collect()
    }

    fn findings(text: &str) -> Vec<String> {
        findings_at("src/lib.rs", text)
    }

    /// Asserts that `text` gives exactly one finding, and that it starts
    /// with `expected`.
    fn assert_one(text: &str, expected: &str) {
        let found = findings(text);
        assert_eq!(found.len(), 1, "{text}\n{found:?}");
        assert!(found[0].starts_with(expected), "{text}\n{found:?}");
    }

    macro_rules! rejects {
        ($($test:ident: $source:expr => $expected:expr;)*) => {$(
            #[test]
            fn $test() {
                assert_one($source, $expected);
            }
        )*};
    }

    rejects! {
        rejects_std_thread:
            "pub fn pause() {\n    std::thread::yield_now();\n}\n"
            => "2: `std::thread` is not allowed in non-test code (`std::thread::yield_now`)";
        rejects_hash_map: "pub type Map = HashMap<u8, u8>;\n" => "1: `HashMap` is not allowed";
        rejects_hash_set: "pub type Set = HashSet<u8>;\n" => "1: `HashSet` is not allowed";
        rejects_random_state: "pub type State = RandomState;\n" => "1: `RandomState` is not allowed";
        rejects_system_time: "pub type Time = SystemTime;\n" => "1: `SystemTime` is not allowed";
        rejects_thread_local:
            "thread_local! {\n    static DEPTH: u8 = 0;\n}\n"
            => "1: `thread_local!` is not allowed";
        rejects_catch_unwind:
            "pub fn run() {\n    let _ = std::panic::catch_unwind(|| ());\n}\n"
            => "2: `catch_unwind` is not allowed";
        rejects_static_mut: "pub static mut COUNT: u8 = 0;\n" => "1: `static mut` is not allowed";
        rejects_constructing_context_outside_the_entry:
            "pub fn run() {\n    let _context = Context::new();\n}\n"
            => "2: `Context` is constructed outside src/main.rs, src/command.rs and src/command/";
    }

    /// Asserts that the method call and both paths of `name` are rejected.
    fn assert_libm(name: &str) {
        let shown = format!(".{name}( calls a transcendental function");
        assert_one(
            &format!("pub fn f(x: f64) -> f64 {{\n    x.{name}(x)\n}}\n"),
            &format!("2: {shown}"),
        );
        for ty in ["f32", "f64"] {
            assert_one(
                &format!("pub fn f(x: {ty}) -> {ty} {{\n    {ty}::{name}(x)\n}}\n"),
                &format!("2: `{ty}::{name}` is a transcendental function"),
            );
        }
    }

    macro_rules! rejects_libm {
        ($($test:ident: $name:literal;)*) => {
            /// The functions that the generated tests cover, in order.
            const COVERED: &[&str] = &[$($name),*];
            $(
                #[test]
                fn $test() {
                    assert_libm($name);
                }
            )*
        };
    }

    rejects_libm! {
        rejects_sin: "sin";
        rejects_cos: "cos";
        rejects_tan: "tan";
        rejects_sin_cos: "sin_cos";
        rejects_asin: "asin";
        rejects_acos: "acos";
        rejects_atan: "atan";
        rejects_atan2: "atan2";
        rejects_sinh: "sinh";
        rejects_cosh: "cosh";
        rejects_tanh: "tanh";
        rejects_asinh: "asinh";
        rejects_acosh: "acosh";
        rejects_atanh: "atanh";
        rejects_exp: "exp";
        rejects_exp2: "exp2";
        rejects_exp_m1: "exp_m1";
        rejects_ln: "ln";
        rejects_log: "log";
        rejects_log2: "log2";
        rejects_log10: "log10";
        rejects_ln_1p: "ln_1p";
        rejects_powf: "powf";
        rejects_cbrt: "cbrt";
        rejects_hypot: "hypot";
    }

    #[test]
    fn the_lists_have_their_frozen_size_and_every_item_has_a_test() {
        // std::thread and static mut, and the names.
        assert_eq!(NAMES.len() + 2, 8);
        assert_eq!(LIBM.len(), 25);
        assert_eq!(COVERED, LIBM);
        let mut unique = LIBM.to_vec();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(unique.len(), LIBM.len());
    }

    #[test]
    fn rejects_every_form_of_a_std_thread_path() {
        for text in [
            "use std::thread;\n",
            "use std::thread::spawn as start;\n",
            "use std::{fmt, thread::JoinHandle};\n",
            "use ::std::thread::*;\n",
            "pub type Handle = ::std::thread::JoinHandle<()>;\n",
            "pub fn f() {\n    let _ = format!(\"{:?}\", std::thread::current());\n}\n",
        ] {
            let found = findings(text);
            assert_eq!(found.len(), 1, "{text}\n{found:?}");
            assert!(
                found[0].contains("`std::thread` is not allowed"),
                "{found:?}"
            );
        }
    }

    #[test]
    fn rejects_denied_items_in_macros_and_their_definitions() {
        for (text, expected) in [
            (
                "pub fn f() {\n    let _ = vec![HashMap::<u8, u8>::new()];\n}\n",
                "2: `HashMap`",
            ),
            (
                "pub fn f(x: f64) {\n    println!(\"{}\", x.sin());\n}\n",
                "2: .sin(",
            ),
            (
                "pub fn f(x: f64) {\n    let _ = [f64::exp(x)];\n    assert!(f32::ln(1.0) == 0.0);\n}\n",
                "3: `f32::ln`",
            ),
            (
                "macro_rules! state {\n    () => {\n        static mut STATE: u8 = 0;\n    };\n}\n",
                "3: `static mut`",
            ),
            (
                "macro_rules! fresh {\n    () => {\n        Context { depth: 0 }\n    };\n}\n",
                "3: `Context` is constructed",
            ),
            (
                "pub fn f() {\n    let _ = vec![Context::default()];\n}\n",
                "2: `Context` is constructed",
            ),
        ] {
            let found = findings(text);
            assert!(
                found.iter().any(|finding| finding.starts_with(expected)),
                "{text}\n{found:?}"
            );
        }
    }

    #[test]
    fn rejects_every_form_of_constructing_context() {
        for text in [
            "pub fn f() -> Context {\n    Context::new(Limits::default())\n}\n",
            "pub fn f() -> Context {\n    Context::default()\n}\n",
            "pub fn f() -> Context {\n    crate::context::Context::default()\n}\n",
            "pub fn f() -> Context {\n    <Context as Default>::default()\n}\n",
            "pub fn f() -> Context {\n    Context { depth: 0 }\n}\n",
            "pub fn f() -> Option<Context> {\n    None.or_else(|| Some(Context::new()))\n}\n",
            "pub fn f() -> Context {\n    Context::with_limits(Limits::default())\n}\n",
            "pub fn f() -> Context {\n    Context::builder().build()\n}\n",
            "pub fn f(limits: Limits) -> Context {\n    Context::from(limits)\n}\n",
            "pub fn f(limits: Limits) -> Context {\n    <Context as From<Limits>>::from(limits)\n}\n",
            "pub fn f() -> Context {\n    Context::<u8>::new()\n}\n",
        ] {
            for path in [
                "src/lib.rs",
                "src/context.rs",
                "src/commands.rs",
                "src/bin/tool.rs",
            ] {
                let found = findings_at(path, text);
                assert_eq!(found.len(), 1, "{path}\n{text}\n{found:?}");
                assert!(
                    found[0].starts_with("2: `Context` is constructed"),
                    "{found:?}"
                );
            }
            for path in ["src/main.rs", "src/command.rs", "src/command/run.rs"] {
                assert_eq!(findings_at(path, text), Vec::<String>::new(), "{path}");
            }
        }
    }

    #[test]
    fn rejects_renaming_or_aliasing_context() {
        for text in [
            "use crate::context::Context as C;\n",
            "use crate::context::{Context as Ctx, Limits};\n",
            "pub type C = crate::context::Context;\n",
            "pub type C = (Context);\n",
            "impl Request for Query {\n    type Ctx = Context;\n}\n",
        ] {
            let at = if text.starts_with("impl") { 2 } else { 1 };
            for path in ["src/lib.rs", "src/context.rs", "src/bin/tool.rs"] {
                let found = findings_at(path, text);
                assert_eq!(
                    found,
                    [format!(
                        "{at}: `Context` is renamed or aliased outside src/main.rs, src/command.rs and src/command/"
                    )],
                    "{path}\n{text}"
                );
            }
            for path in ["src/main.rs", "src/command.rs", "src/command/run.rs"] {
                assert_eq!(findings_at(path, text), Vec::<String>::new(), "{path}");
            }
        }
        for text in [
            "use crate::context::Context;\n",
            "use crate::context::Context as _;\n",
            "use crate::context::Context as Context;\n",
            "pub type Context = crate::context::Context;\n",
            "pub type Limits = crate::context::Limits;\n",
            "pub type Pair = (Context, Context);\n",
        ] {
            assert_eq!(findings(text), Vec::<String>::new(), "{text}");
        }
    }

    #[test]
    fn denied_items_in_test_code_pass() {
        let text = r#"
pub fn library() {}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};
    use std::thread;

    static mut COUNT: u8 = 0;

    thread_local! {
        static DEPTH: u8 = 0;
    }

    #[test]
    fn everything() {
        let _ = std::panic::catch_unwind(|| 1.0_f64.sin());
        let _ = f64::exp(1.0) + 2.0_f64.powf(0.5);
        let _ = (std::time::SystemTime::now(), std::hash::RandomState::new());
        let _ = Context::new();
        thread::spawn(|| ());
    }
}

#[test]
fn a_test_outside_a_test_module() {
    let _ = HashMap::<u8, u8>::new();
}

#[cfg(all(unix, test))]
fn only_in_unix_tests() -> f64 {
    1.0_f64.cos()
}

#[cfg(any(test, all(test, unix)))]
static mut ONLY_IN_TESTS: u8 = 0;

pub struct Value;

impl Value {
    #[cfg(test)]
    fn sample() -> HashSet<u8> {
        HashSet::new()
    }
}

pub fn statements() {
    #[cfg(test)]
    let _ = SystemTime::now();
    #[cfg(test)]
    println!("{}", 2.0_f64.ln());
}
"#;
        assert_eq!(findings(text), Vec::<String>::new());
    }

    #[test]
    fn code_that_is_not_only_test_code_is_scanned() {
        for text in [
            "#[cfg(not(test))]\npub type Map = HashMap<u8, u8>;\n",
            "#[cfg(any(test, unix))]\npub type Map = HashMap<u8, u8>;\n",
            "#[cfg(feature = \"test\")]\npub type Map = HashMap<u8, u8>;\n",
            "#[cfg_attr(test, derive(Debug))]\npub struct Map(HashMap<u8, u8>);\n",
        ] {
            assert_eq!(findings(text).len(), 1, "{text}");
        }
    }

    #[test]
    fn denied_names_in_comments_and_strings_pass() {
        let text = r##"
//! Never `HashMap`, `std::thread::spawn`, `x.sin()` or `Context::new()`.

// A comment that names HashSet, SystemTime and f64::exp(x).
/* A block comment: thread_local! { static mut X: u8 = 0; } */

/// Documentation that names `catch_unwind`, `RandomState` and `x.powf(y)`.
#[doc = "std::thread::sleep and Context { depth: 0 }"]
pub fn text() -> [&'static str; 3] {
    let _ = format!("{} x.sin() {}", "HashMap", "static mut");
    ["std::thread", r#"f64::cos(x) Context::default()"#, concat!("x.ln(", ")")]
}
"##;
        assert_eq!(findings(text), Vec::<String>::new());
    }

    #[test]
    fn names_that_do_not_match_pass() {
        let text = r#"
pub struct HashMapLike;
pub struct Sine {
    pub sin: f64,
}
pub struct MyContext;

pub fn names(x: f64, value: &Sine, context: &Context) -> f64 {
    let _ = (HashMapLike, MyContext::new(), context.limits());
    let _ = (x.sqrt(), f64::sqrt(x), x.sine(), sin(x), value.sin, x.exp_fast());
    let _ = (f64::consts::E, crate::exp::run(), self::cos::run());
    let _ = std_thread::run();
    value.sin
}
"#;
        assert_eq!(findings(text), Vec::<String>::new());
    }

    /// The findings in `text` with the std allow list `entries`.
    fn std_findings(text: &str, entries: &[&str]) -> Vec<String> {
        let entries: Vec<String> = entries.iter().map(|entry| entry.to_string()).collect();
        let allowed = |path: &str| crate::guard::std_allows(&entries, path);
        scan("src/lib.rs", text, &allowed)
            .expect("the source parses")
            .findings
            .iter()
            .map(|finding| format!("{}: {}", finding.line, finding.message))
            .collect()
    }

    #[test]
    fn rejects_a_std_path_outside_the_allow_list() {
        assert_eq!(
            std_findings("use std::fs::read;\n", &["std::fmt", "std::io::stdin"]),
            ["1: std path `std::fs::read` is not in guard/std-paths.txt"]
        );
    }

    #[test]
    fn checks_std_paths_in_every_position() {
        let list = [
            "std::fmt",
            "std::io::stdin",
            "std::io::Write",
            "std::process::ExitCode",
        ];
        let allowed = r#"
use std::fmt::{self, Display};
use std::fmt::*;
use std::io::Write as _;
use std::process::ExitCode;

pub fn f(out: &mut dyn std::io::Write) -> std::process::ExitCode {
    let _ = std::io::stdin();
    let _ = std::io::Write::flush(out);
    let _ = format!("{}", std::fmt::Error);
    ExitCode::SUCCESS
}
"#;
        assert_eq!(std_findings(allowed, &list), Vec::<String>::new());
        for (text, path) in [
            ("use std::io;\n", "std::io"),
            ("use std::{fmt, io::Read};\n", "std::io::Read"),
            ("use std::io::*;\n", "std::io"),
            ("use std::*;\n", "std"),
            ("use std as standard;\n", "std"),
            ("extern crate std as standard;\n", "std"),
            (
                "pub fn f() {\n    let _ = ::std::fs::read(\"x\");\n}\n",
                "std::fs::read",
            ),
            ("pub type R = std::io::WriteFmt;\n", "std::io::WriteFmt"),
            ("pub fn f() {\n    std::println!();\n}\n", "std::println"),
            (
                "pub fn f() {\n    let _ = vec![std::process::id()];\n}\n",
                "std::process::id",
            ),
            (
                "#[derive(std::hash::Hash)]\npub struct S;\n",
                "std::hash::Hash",
            ),
        ] {
            let found = std_findings(text, &list);
            assert!(
                found.iter().any(|finding| finding
                    .ends_with(&format!("std path `{path}` is not in guard/std-paths.txt"))),
                "{text}\n{found:?}"
            );
        }
    }

    #[test]
    fn reports_test_module_files() {
        let scanned = |path: &str, text: &str| scan(path, text, &|_| true).unwrap().test_modules;
        let text = "#[cfg(test)]\nmod tests;\nmod inner {\n    #[cfg(test)]\n    mod tests;\n}\nmod plain;\n#[cfg(test)]\n#[path = \"elsewhere.rs\"]\nmod moved;\n";
        assert_eq!(
            scanned("src/lib.rs", text),
            ["src/tests", "src/inner/tests"]
        );
        assert_eq!(
            scanned("src/expr.rs", text),
            ["src/expr/tests", "src/expr/inner/tests"]
        );
        assert_eq!(
            scanned("src/expr/mod.rs", text),
            ["src/expr/tests", "src/expr/inner/tests"]
        );
        let moved = "#[path = \"other\"]\nmod inner {\n    #[cfg(test)]\n    mod tests;\n}\n";
        assert_eq!(scanned("src/lib.rs", moved), Vec::<String>::new());
    }

    #[test]
    fn reports_modules_declared_as_non_test_code() {
        let modules = |path: &str, text: &str| scan(path, text, &|_| true).unwrap().modules;
        let text = "#[cfg(test)]\nmod tests;\nmod inner {\n    mod deep;\n}\nmod plain;\n#[path = \"x.rs\"]\nmod moved;\n#[cfg(test)]\nmod checks {\n    mod helpers;\n}\n";
        assert_eq!(modules("src/lib.rs", text), ["src/inner/deep", "src/plain"]);
        assert_eq!(
            modules("src/expr.rs", text),
            ["src/expr/inner/deep", "src/expr/plain"]
        );
        assert_eq!(modules("src/bin/tool.rs", "mod util;\n"), ["src/bin/util"]);
        assert_eq!(modules("build.rs", "mod util;\n"), ["util"]);
    }

    #[test]
    fn a_file_that_does_not_parse_is_a_finding() {
        let error = scan("src/lib.rs", "pub fn f( {\n", &|_| true).unwrap_err();
        assert!(error.message.starts_with("cannot parse"), "{error:?}");
    }
}
