use derive_ex::Ex;
use proc_macro2::{Group, Spacing, Span, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use std::{
    collections::{BTreeMap, HashSet},
    iter::once,
    ops::Deref,
};
use structmeta::{Parse, ToTokens};
use syn::{
    ext::IdentExt,
    parse::Parse,
    parse2, parse_str,
    punctuated::Punctuated,
    spanned::Spanned,
    token::Comma,
    visit::{visit_path, visit_type, Visit},
    Attribute, DeriveInput, Expr, Field, GenericParam, Generics, Ident, Lit, Meta, Path, Result,
    Token, Type, WherePredicate,
};

macro_rules! bail {
    (_, $($arg:tt)*) => {
        bail!(::proc_macro2::Span::call_site(), $($arg)*)
    };
    ($span:expr, $fmt:literal $(,)?) => {
        return ::std::result::Result::Err(::syn::Error::new($span, ::std::format!($fmt)))
    };
    ($span:expr, $fmt:literal, $($arg:tt)*) => {
        return ::std::result::Result::Err(::syn::Error::new($span, ::std::format!($fmt, $($arg)*)))
    };
}

pub fn into_macro_output(input: Result<TokenStream>) -> proc_macro::TokenStream {
    match input {
        Ok(s) => s,
        Err(e) => e.to_compile_error(),
    }
    .into()
}

#[derive(Parse)]
pub struct Args(#[parse(terminated)] pub Punctuated<Arg, Comma>);

impl Args {
    pub fn new() -> Self {
        Self(Punctuated::new())
    }
    pub fn expect_single_value(&self, span: Span) -> Result<&Expr> {
        if self.len() != 1 {
            bail!(
                span,
                "expect 1 arguments, but supplied {} arguments.",
                self.len()
            );
        }
        match &self[0] {
            Arg::Value(expr) => Ok(expr),
            Arg::NameValue { .. } => bail!(span, "expected unnamed argument."),
        }
    }
}
impl Default for Args {
    fn default() -> Self {
        Self::new()
    }
}
impl Deref for Args {
    type Target = Punctuated<Arg, Comma>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl IntoIterator for Args {
    type Item = Arg;
    type IntoIter = <Punctuated<Arg, Comma> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(ToTokens, Parse)]
pub enum Arg {
    NameValue {
        #[parse(peek, any)]
        name: Ident,
        #[parse(peek)]
        eq_token: Token![=],
        value: Expr,
    },
    Value(Expr),
}

pub struct SharpVals {
    allow_vals: bool,
    allow_self: bool,
    pub vals: BTreeMap<FieldKey, Span>,
    pub self_span: Option<Span>,
}
impl SharpVals {
    pub fn new(allow_vals: bool, allow_self: bool) -> Self {
        Self {
            allow_vals,
            allow_self,
            vals: BTreeMap::new(),
            self_span: None,
        }
    }
    pub fn expand(&mut self, input: TokenStream) -> Result<TokenStream> {
        let mut tokens = Vec::new();
        let mut iter = input.into_iter().peekable();
        while let Some(t) = iter.next() {
            match &t {
                TokenTree::Group(g) => {
                    let mut g_new =
                        TokenTree::Group(Group::new(g.delimiter(), self.expand(g.stream())?));
                    g_new.set_span(g.span());
                    tokens.push(g_new);
                    continue;
                }
                TokenTree::Punct(p) => {
                    if p.as_char() == '#' && p.spacing() == Spacing::Alone {
                        if let Some(token) = iter.peek() {
                            if let Some(key) = FieldKey::try_from_token(token) {
                                let span = token.span();
                                let allow = if &key == "self" {
                                    self.self_span.get_or_insert(span);
                                    self.allow_self
                                } else {
                                    self.vals.entry(key.clone()).or_insert(span);
                                    self.allow_vals
                                };
                                if !allow {
                                    bail!(span, "cannot use `#{}` in this position.", key);
                                }
                                if self.self_span.is_some() {
                                    if let Some(key) = self.vals.keys().next() {
                                        bail!(span, "cannot use both `#self` and `#{}`", key);
                                    }
                                }
                                let ident = key.to_dummy_ident_with_span(span);
                                tokens.extend(ident.to_token_stream());
                                iter.next();
                                continue;
                            }
                        }
                    }
                }
                _ => {}
            }
            tokens.extend(once(t));
        }
        Ok(tokens.into_iter().collect())
    }

    pub fn expand_args<T: Parse>(&mut self, meta: &Meta) -> Result<T> {
        match meta {
            Meta::List(m) => parse2(self.expand(m.tokens.clone())?),
            Meta::Path(_) | Meta::NameValue(_) => {
                let span = span_in_args(meta);
                bail!(span, "expected arguments.")
            }
        }
    }
    pub fn expand_args_or_default<T: Parse + Default>(&mut self, meta: &Meta) -> Result<T> {
        match meta {
            Meta::List(m) => parse2(self.expand(m.tokens.clone())?),
            Meta::Path(_) => Ok(T::default()),
            Meta::NameValue(m) => bail!(
                m.eq_token.span(),
                "`name = value` style attribute was not supported."
            ),
        }
    }
}

#[derive(Clone, Debug, Ex)]
#[derive_ex(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldKey {
    raw: RawFieldKey,
    #[ord(ignore)]
    span: Span,
}
impl FieldKey {
    pub fn from_field(idx: usize, field: &Field) -> Self {
        Self {
            raw: RawFieldKey::from_field(idx, field),
            span: field.span(),
        }
    }
    pub fn try_from_token(token: &TokenTree) -> Option<Self> {
        RawFieldKey::try_from_token(token).map(|raw| Self {
            raw,
            span: token.span(),
        })
    }
    pub fn to_dummy_ident(&self) -> Ident {
        Ident::new(&format!("_{}", self.raw), self.span)
    }
    pub fn to_dummy_ident_with_span(&self, span: Span) -> Ident {
        Ident::new(&format!("_{}", self.raw), span)
    }
    pub fn to_valid_ident(&self) -> Option<Ident> {
        self.raw.to_valid_ident()
    }
}

impl PartialEq<str> for FieldKey {
    fn eq(&self, other: &str) -> bool {
        self.raw == *other
    }
}
impl std::fmt::Display for FieldKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.raw.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
enum RawFieldKey {
    Named(String),
    Unnamed(usize),
}

impl RawFieldKey {
    fn from_ident(ident: &Ident) -> Self {
        Self::Named(ident.unraw().to_string())
    }
    fn from_field(idx: usize, field: &Field) -> Self {
        if let Some(ident) = &field.ident {
            Self::from_ident(ident)
        } else {
            Self::Unnamed(idx)
        }
    }
    fn try_from_token(token: &TokenTree) -> Option<Self> {
        match token {
            TokenTree::Ident(ident) => Some(Self::from_ident(ident)),
            TokenTree::Literal(token) => {
                if let Lit::Int(lit) = Lit::new(token.clone()) {
                    if lit.suffix().is_empty() {
                        if let Ok(idx) = lit.base10_parse() {
                            return Some(Self::Unnamed(idx));
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn to_valid_ident(&self) -> Option<Ident> {
        match self {
            Self::Named(name) => to_valid_ident(name).ok(),
            Self::Unnamed(..) => None,
        }
    }
}
impl PartialEq<str> for RawFieldKey {
    fn eq(&self, other: &str) -> bool {
        match self {
            Self::Named(name) => name == other,
            _ => false,
        }
    }
}
impl std::fmt::Display for RawFieldKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Named(name) => name.fmt(f),
            Self::Unnamed(idx) => idx.fmt(f),
        }
    }
}

pub struct GenericParamSet {
    idents: HashSet<Ident>,
}

impl GenericParamSet {
    pub fn new(generics: &Generics) -> Self {
        let mut idents = HashSet::new();
        for p in &generics.params {
            match p {
                GenericParam::Type(t) => {
                    idents.insert(t.ident.unraw());
                }
                GenericParam::Const(t) => {
                    idents.insert(t.ident.unraw());
                }
                _ => {}
            }
        }
        Self { idents }
    }
    fn contains(&self, ident: &Ident) -> bool {
        self.idents.contains(&ident.unraw())
    }

    pub fn contains_in_type(&self, ty: &Type) -> bool {
        struct Visitor<'a> {
            generics: &'a GenericParamSet,
            result: bool,
        }
        impl<'ast> Visit<'ast> for Visitor<'_> {
            fn visit_path(&mut self, i: &'ast syn::Path) {
                if i.leading_colon.is_none() {
                    if let Some(s) = i.segments.iter().next() {
                        if self.generics.contains(&s.ident) {
                            self.result = true;
                        }
                    }
                }
                visit_path(self, i);
            }
        }
        let mut visitor = Visitor {
            generics: self,
            result: false,
        };
        visit_type(&mut visitor, ty);
        visitor.result
    }
}

pub fn impl_trait(
    input: &DeriveInput,
    trait_path: &Path,
    wheres: &[WherePredicate],
    contents: TokenStream,
) -> TokenStream {
    let ty = &input.ident;
    let (impl_g, ty_g, where_clause) = input.generics.split_for_impl();
    let mut wheres = wheres.to_vec();
    if let Some(where_clause) = where_clause {
        wheres.extend(where_clause.predicates.iter().cloned());
    }
    let where_clause = if wheres.is_empty() {
        quote! {}
    } else {
        quote! { where #(#wheres,)*}
    };
    quote! {
        #[automatically_derived]
        impl #impl_g #trait_path for #ty #ty_g #where_clause {
            #contents
        }
    }
}
pub fn impl_trait_result(
    input: &DeriveInput,
    trait_path: &Path,
    wheres: &[WherePredicate],
    contents: TokenStream,
    dump: bool,
) -> Result<TokenStream> {
    let ts = impl_trait(input, trait_path, wheres, contents);
    if dump {
        panic!("macro result: \n{ts}");
    }
    Ok(ts)
}

pub fn to_valid_ident(s: &str) -> Result<Ident> {
    if let Ok(ident) = parse_str(s) {
        Ok(ident)
    } else {
        parse_str(&format!("r#{s}"))
    }
}

pub fn parse_from_attrs<T: Parse + Default>(attrs: &[Attribute], name: &str) -> Result<T> {
    let mut a = None;
    for attr in attrs {
        if attr.path().is_ident(name) {
            if a.is_some() {
                bail!(attr.span(), "attribute `{}` can specified only once", name);
            }
            a = Some(attr);
        }
    }
    if let Some(a) = a {
        a.parse_args()
    } else {
        Ok(T::default())
    }
}

pub fn span_in_args(meta: &Meta) -> Span {
    match meta {
        Meta::Path(_) => meta.span(),
        Meta::List(m) => m.delimiter.span().span(),
        Meta::NameValue(m) => m.value.span(),
    }
}
