use std::{collections::HashMap, mem::take};

use crate::syn_utils::{
    impl_trait_result, parse_parenthesized_args, to_valid_ident, Arg, Args, FieldKey,
    GenericParamSet, SharpVals,
};
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use std::fmt::Write;
use syn::{
    ext::IdentExt,
    parenthesized,
    parse::discouraged::Speculative,
    parse::{Parse, ParseStream},
    parse2, parse_quote, parse_str,
    punctuated::Punctuated,
    spanned::Spanned,
    token::Comma,
    token::Dot2,
    Attribute, Data, DataEnum, DataStruct, DeriveInput, Expr, Fields, Ident, Index, Lit, Member,
    Path, Result, Token, Type, WherePredicate,
};

pub fn derive_arbitrary(input: DeriveInput) -> Result<TokenStream> {
    let mut dump = false;
    let mut type_parameters = quote! {
        type Parameters = ()
    };
    let mut bound_exists = false;
    let mut bound_default = false;
    let mut bound_types = Vec::new();
    let mut bound_predicates = Vec::new();
    for attr in &input.attrs {
        if attr.path.is_ident("arbitrary") {
            let args = attr.parse_args_with(Punctuated::<ArbitraryArg, Comma>::parse_terminated)?;
            for arg in args {
                match arg {
                    ArbitraryArg::Args(ty) => {
                        type_parameters = quote_spanned!(ty.span()=> type Parameters = #ty);
                    }
                    ArbitraryArg::Dump => {
                        dump = true;
                    }
                    ArbitraryArg::Bound(bounds) => {
                        bound_exists = true;
                        for bound in bounds.iter() {
                            match bound {
                                Bound::Type(ty) => bound_types.push(ty.clone()),
                                Bound::Predicate(p) => bound_predicates.push(p.clone()),
                                Bound::Default(..) => bound_default = true,
                            }
                        }
                    }
                }
            }
        }
    }

    let mut bound_types_default = Vec::new();
    let expr = match &input.data {
        Data::Struct(data) => expr_for_struct(&input, data, &mut bound_types_default)?,
        Data::Enum(data) => expr_for_enum(&input, data, &mut bound_types_default)?,
        _ => bail!(
            input.span(),
            "`#[derive(Arbitrary)]` supports only enum and struct."
        ),
    };
    if !bound_exists || bound_default {
        bound_types.extend(bound_types_default);
    }
    for ty in bound_types {
        bound_predicates.push(parse_quote!(#ty : proptest::arbitrary::Arbitrary + 'static));
    }
    impl_trait_result(
        &input,
        &parse_quote!(proptest::arbitrary::Arbitrary),
        &bound_predicates,
        quote! {
            #type_parameters;
            type Strategy = proptest::strategy::BoxedStrategy<Self>;
            fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
                #[allow(dead_code)]
                fn _to_fn_ptr<T>(f: fn(&T) -> bool) -> fn(&T) -> bool {
                    f
                }
                let args = std::rc::Rc::new(args);
                proptest::strategy::Strategy::boxed(#expr)
            }
        },
        dump,
    )
}
fn expr_for_struct(
    input: &DeriveInput,
    data: &DataStruct,
    bound_types: &mut Vec<Type>,
) -> Result<TokenStream> {
    let generics = GenericParamSet::new(&input.generics);
    expr_for_fields(
        parse_quote!(Self),
        &generics,
        &data.fields,
        &input.attrs,
        true,
        bound_types,
    )
}
fn expr_for_enum(
    input: &DeriveInput,
    data: &DataEnum,
    bound_types: &mut Vec<Type>,
) -> Result<TokenStream> {
    if data.variants.is_empty() {
        bail!(Span::call_site(), "zero variant enum was not supported.");
    }
    let generics = GenericParamSet::new(&input.generics);
    let mut exprs = Vec::new();
    for variant in &data.variants {
        let mut weight = None;
        for attr in &variant.attrs {
            if attr.path.is_ident("weight") {
                if weight.is_some() {
                    bail!(attr.span(), "`#[weight]` can specify only once.");
                }
                weight = Some(attr.parse_args::<WeightArg>()?);
            }
        }
        let weight = if let Some(arg) = weight {
            if arg.is_zero() {
                continue;
            } else {
                let expr = arg.expr;
                quote_spanned!(expr.span()=>  _to_weight(#expr))
            }
        } else {
            quote!(1)
        };
        let variant_ident = &variant.ident;
        let expr = expr_for_fields(
            parse_quote!(Self::#variant_ident),
            &generics,
            &variant.fields,
            &variant.attrs,
            false,
            bound_types,
        )?;
        exprs.push(quote! {#weight=> #expr});
    }
    let s: Ident = parse_quote!(_s);
    let filter_lets = Filter::from_enum_attrs_make_let(&input.attrs, &s)?;
    Ok(quote! {
        {
            #[allow(dead_code)]
            fn _to_weight(weight: u32) -> u32 { weight }
            let #s = proptest::prop_oneof![#(#exprs,)*];
            #filter_lets
            #s
        }
    })
}
fn expr_for_fields(
    self_path: Path,
    generics: &GenericParamSet,
    fields: &Fields,
    attrs: &[Attribute],
    filter_allow_fn: bool,
    bound_types: &mut Vec<Type>,
) -> Result<TokenStream> {
    let b = StrategyBuilder::from_fields(self_path, fields, attrs, filter_allow_fn)?;
    bound_types.extend(b.get_bound_types(generics));
    b.build()
}

struct WeightArg {
    expr: Expr,
}
impl Parse for WeightArg {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            expr: input.parse()?,
        })
    }
}
impl WeightArg {
    fn is_zero(&self) -> bool {
        if let Expr::Lit(lit) = &self.expr {
            if let Lit::Int(lit) = &lit.lit {
                if let Ok(value) = lit.base10_parse::<u32>() {
                    return value == 0;
                }
            }
        }
        false
    }
}

struct AnyArgs {
    initializer: Option<Expr>,
    setters: Vec<(Ident, Expr)>,
}
impl AnyArgs {
    fn empty() -> Self {
        Self {
            initializer: None,
            setters: Vec::new(),
        }
    }
    fn parse(args: Args) -> Result<Self> {
        let mut initializer = None;
        let mut setters = Vec::new();
        for arg in args {
            match arg {
                Arg::NameValue { name, value, .. } => {
                    setters.push((name, value));
                }
                Arg::Value(value) => {
                    if initializer.is_some() {
                        bail!(value.span(), "Unnamed argument can be specified only once.");
                    }
                    initializer = Some(value);
                }
            }
        }
        Ok(Self {
            initializer,
            setters,
        })
    }
    fn into_strategy(self, ty: &Type) -> TokenStream {
        if self.initializer.is_none() && self.setters.is_empty() {
            quote!(proptest::arbitrary::any::<#ty>())
        } else {
            let init = self
                .initializer
                .unwrap_or_else(|| parse_quote!(std::default::Default::default()));
            if self.setters.is_empty() {
                quote!(proptest::arbitrary::any_with::<#ty>(#init))
            } else {
                let setters = self.setters.into_iter().map(|(name, expr)| {
                    let member = ident_to_member(name);
                    quote!(_any_args.#member = #expr;)
                });
                quote! {
                    {
                        let mut _any_args : <#ty as proptest::arbitrary::Arbitrary>::Parameters = #init;
                        #(#setters)*
                        proptest::arbitrary::any_with::<#ty>(_any_args)
                    }
                }
            }
        }
    }
}

struct ArbitraryArgs {
    pub args: Punctuated<ArbitraryArg, Comma>,
}
impl Parse for ArbitraryArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            args: Punctuated::parse_terminated(input)?,
        })
    }
}

enum ArbitraryArg {
    Args(Type),
    Bound(Punctuated<Bound, Token![,]>),
    Dump,
}
impl Parse for ArbitraryArg {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Ident) {
            let name: Ident = input.parse()?;
            if name == "args" {
                let _eq_token: Token![=] = input.parse()?;
                return Ok(ArbitraryArg::Args(input.parse()?));
            }
            if name == "bound" {
                let conetnt;
                let _paren_token = parenthesized!(conetnt in input);
                return Ok(ArbitraryArg::Bound(Punctuated::parse_terminated(&conetnt)?));
            }
            if name == "dump" {
                return Ok(ArbitraryArg::Dump);
            }
        }
        Err(input.error("usage : #[arbitrary(args = T, bound(T, T, ..), dump)]"))
    }
}

// enum Quotable<T> {
//     Direct(T),
//     Quoted(ItemsOf<T>),
// }
// impl<T: Parse> Parse for Quotable<T> {
//     fn parse(input: ParseStream) -> Result<Self> {
//         let fork = input.fork();
//         if let Ok(lit) = fork.parse::<LitStr>() {
//             input.advance_to(&fork);
//             let token: TokenStream = parse_str(&lit.value())?;
//             let tokens = quote_spanned!(lit.span()=> #token);
//             Ok(Quotable::Quoted(parse2(tokens)?))
//         } else {
//             Ok(Quotable::Direct(input.parse()?))
//         }
//     }
// }
// impl<T> Quotable<T> {
//     fn into_iter(self) -> impl IntoIterator<Item = T> {
//         let items = match self {
//             Self::Direct(item) => vec![item],
//             Self::Quoted(items) => items.items.into_iter().collect(),
//         };
//         items.into_iter()
//     }
// }

// struct ItemsOf<T> {
//     items: Punctuated<T, Token![,]>,
// }
// impl<T: Parse> Parse for ItemsOf<T> {
//     fn parse(input: ParseStream) -> Result<Self> {
//         Ok(Self {
//             items: Punctuated::parse_terminated(input)?,
//         })
//     }
// }
// impl<T> ItemsOf<T> {
//     fn into_iter(self) -> impl Iterator<Item = T> {
//         self.items.into_iter()
//     }
// }
// impl<T> ItemsOf<Quotable<T>> {
//     fn into_flatten(self) -> impl Iterator<Item = T> {
//         self.into_iter().flat_map(|x| x.into_iter())
//     }
// }

#[allow(clippy::large_enum_variant)]
enum Bound {
    Type(Type),
    Predicate(WherePredicate),
    Default(Dot2),
}
impl Parse for Bound {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Dot2) {
            return Ok(Self::Default(input.parse()?));
        }
        let fork = input.fork();
        match fork.parse() {
            Ok(p) => {
                input.advance_to(&fork);
                Ok(Self::Predicate(p))
            }
            Err(e) => {
                if let Ok(ty) = input.parse() {
                    Ok(Self::Type(ty))
                } else {
                    Err(e)
                }
            }
        }
    }
}

struct Filter {
    whence: Expr,
    fun: Expr,
}
impl Filter {
    fn parse(span: Span, args: Args) -> Result<Self> {
        let mut values = Vec::new();
        for arg in args {
            match arg {
                Arg::Value(value) => {
                    values.push(value);
                }
                Arg::NameValue { .. } => bail!(arg.span(), "named argument was not supported."),
            }
        }
        let whence;
        let fun;
        match values.len() {
            1 => {
                let mut iter = values.into_iter();
                fun = iter.next().unwrap();
                let whence_str = fun.to_token_stream().to_string();
                whence = parse_quote!(#whence_str);
            }
            2 => {
                let mut iter = values.into_iter();
                whence = iter.next().unwrap();
                fun = iter.next().unwrap();
            }
            _ => bail!(
                span,
                "expected `#[filter(whence, fun)]` or `#[filter(fun)]`."
            ),
        }
        Ok(Self { whence, fun })
    }
    fn from_enum_attrs_make_let(attrs: &[Attribute], ident: &Ident) -> Result<TokenStream> {
        let mut results = TokenStream::new();
        for attr in attrs {
            if attr.path.is_ident("filter") {
                let mut sharp_vals = SharpVals::new(false, true);
                let ts = sharp_vals.expand(attr.tokens.clone())?;
                let filter = Filter::parse(attr.span(), parse2(ts)?)?;
                let code = if sharp_vals.self_span.is_some() {
                    filter.make_let_self(ident)
                } else {
                    let self_ty: Type = parse_quote!(Self);
                    filter.make_let(&self_ty, ident)
                };
                results.extend(code);
            }
        }
        Ok(results)
    }
    fn make_let(&self, ty: &Type, ident: &Ident) -> TokenStream {
        let Self { whence, fun } = self;
        quote_spanned! {fun.span()=>
            let #ident = proptest::strategy::Strategy::prop_filter(#ident, #whence, _to_fn_ptr::<#ty>(#fun));
        }
    }
    fn make_let_field(&self, ident: &Ident, field: &Ident, by_ref: bool) -> TokenStream {
        let Self { whence, fun } = self;
        let let_clone = if by_ref {
            quote! {}
        } else {
            quote! { let #field = std::clone::Clone::clone(#field); }
        };
        quote_spanned! {fun.span()=>
            let #ident = {
                #[allow(dead_code)]
                let args = std::clone::Clone::clone(&args);
                proptest::strategy::Strategy::prop_filter(#ident, #whence, move |#field| {
                    let args = std::ops::Deref::deref(&args);
                    #let_clone
                    #fun
                })
            };
        }
    }
    fn make_let_self(&self, ident: &Ident) -> TokenStream {
        let Self { whence, fun } = self;
        quote_spanned! {fun.span()=>
            let #ident = {
                #[allow(dead_code)]
                let args = std::clone::Clone::clone(&args);
                proptest::strategy::Strategy::prop_filter(#ident, #whence, move |_self| {
                    let args = std::ops::Deref::deref(&args);
                    #fun
                })
            };
        }
    }
}

struct StrategyBuilder {
    ts: TokenStream,
    items: Vec<StrategyItem>,
    self_path: Path,
    fields: Fields,
    filters_fields: Vec<FilterItem>,
    filters_self: Vec<Filter>,
    filters_fn: Vec<Filter>,
}

struct StrategyItem {
    idx: usize,
    key: FieldKey,
    by_ref: bool,
    is_any: bool,
    strategy: Expr,
    dependency: Vec<usize>,

    group: Option<usize>,
    group_next: Option<usize>,

    offset: Option<usize>,
    offset_next: Option<usize>,

    group_items: Vec<usize>,
    group_items_next: Vec<usize>,
    group_dependency: Vec<usize>,
    group_offset: Option<usize>,
}

struct FilterItem {
    filter: Filter,
    vals: Vec<usize>,
}

impl StrategyBuilder {
    fn from_fields(
        self_path: Path,
        fields: &Fields,
        attrs: &[Attribute],
        filter_allow_self: bool,
    ) -> Result<Self> {
        let ts = TokenStream::new();
        let mut key_to_idx = HashMap::new();
        for (idx, field) in fields.iter().enumerate() {
            key_to_idx.insert(FieldKey::from_field(idx, field), idx);
        }
        let mut items = Vec::new();
        let mut filters_fields = Vec::new();
        for (idx, field) in fields.iter().enumerate() {
            let key = FieldKey::from_field(idx, field);
            let func_ident = format!("_strategy_of_{}", key);
            let mut strategy = None;
            let mut filters_fn = Vec::new();
            let mut filters_field = Vec::new();
            let mut sharp_vals = SharpVals::new(true, false);
            let mut by_ref = false;
            let mut is_any = false;
            for attr in &field.attrs {
                let is_strategy_attr = attr.path.is_ident("strategy");
                let is_any_attr = attr.path.is_ident("any");
                if strategy.is_some() && (is_strategy_attr || is_any_attr) {
                    bail!(
                        attr.span(),
                        "`#[any]` and `#[strategy]` can only be specified once in total."
                    );
                }
                if is_strategy_attr {
                    let ts = sharp_vals.expand(attr.tokens.clone())?;
                    let args = parse_parenthesized_args(ts)?;
                    let value = args.expect_single_value(attr.span())?;
                    let func_ident = Ident::new(&func_ident, value.span());
                    let ty = &field.ty;
                    strategy = Some(quote_spanned!(value.span()=> #func_ident::<#ty, _>(#value)));
                }
                if is_any_attr {
                    is_any = true;
                    let ts = sharp_vals.expand(attr.tokens.clone())?;
                    let any_attr = AnyArgs::parse(parse_parenthesized_args(ts)?)?;
                    strategy = Some(any_attr.into_strategy(&field.ty));
                }
                if attr.path.is_ident("by_ref") {
                    if !attr.tokens.is_empty() {
                        bail!(
                            attr.tokens.span(),
                            "Brackets and arguments are not allowed."
                        );
                    }
                    by_ref = true;
                }
                if attr.path.is_ident("filter") {
                    let mut sharp_vals = SharpVals::new(true, false);
                    let ts = sharp_vals.expand(attr.tokens.clone())?;
                    let filter = Filter::parse(attr.span(), parse_parenthesized_args(ts)?)?;
                    if sharp_vals.vals.is_empty() {
                        filters_fn.push(filter);
                    } else if sharp_vals.vals.contains_key(&key) {
                        if sharp_vals.vals.len() == 1 {
                            filters_field.push(filter);
                        } else {
                            let vals = to_idxs(&sharp_vals.vals, &key_to_idx)?;
                            filters_fields.push(FilterItem { filter, vals });
                        }
                    } else {
                        bail!(attr.span(), "`#{}` is not used.", key);
                    }
                }
            }
            let s: Ident = parse_quote! { _s };
            let ty = &field.ty;
            let strategy = if let Some(strategy) = strategy {
                strategy
            } else {
                is_any = true;
                AnyArgs::empty().into_strategy(ty)
            };
            let mut filter_lets = Vec::new();
            for filter in filters_field {
                filter_lets.push(filter.make_let_field(&s, &key.to_dummy_ident(), by_ref));
            }
            for filter in filters_fn {
                filter_lets.push(filter.make_let(ty, &s));
            }
            let func_ident = Ident::new(&func_ident, Span::call_site());
            let func = quote_spanned! {ty.span()=>
                #[allow(dead_code)]
                fn #func_ident<T: std::fmt::Debug, S: proptest::strategy::Strategy<Value = T>>(s: S) -> impl proptest::strategy::Strategy<Value = T> { s }
            };
            let strategy = parse_quote! {
                {
                    #func
                    let #s = #strategy;
                    #(#filter_lets)*
                    #s
                }
            };
            let dependency = to_idxs(&sharp_vals.vals, &key_to_idx)?;
            items.push(StrategyItem::new(
                idx, key, by_ref, is_any, strategy, dependency,
            ));
        }
        let mut filters_fn = Vec::new();
        let mut filters_self = Vec::new();
        for attr in attrs {
            if attr.path.is_ident("filter") {
                let mut sharp_vals = SharpVals::new(true, filter_allow_self);
                let ts = sharp_vals.expand(attr.tokens.clone())?;
                let filter = Filter::parse(attr.span(), parse2(ts)?)?;
                if !sharp_vals.vals.is_empty() {
                    let vals = to_idxs(&sharp_vals.vals, &key_to_idx)?;
                    filters_fields.push(FilterItem { filter, vals });
                } else if sharp_vals.self_span.is_some() {
                    filters_self.push(filter);
                } else {
                    filters_fn.push(filter);
                }
            }
        }
        let fields = fields.clone();
        Ok(Self {
            ts,
            items,
            self_path,
            fields,
            filters_fields,
            filters_self,
            filters_fn,
        })
    }
    fn get_bound_types(&self, generics: &GenericParamSet) -> Vec<Type> {
        let mut bound_types = Vec::new();
        for (idx, field) in self.fields.iter().enumerate() {
            if self.items[idx].is_any {
                let ty = &field.ty;
                if generics.contains_in_type(ty) {
                    bound_types.push(ty.clone());
                }
            }
        }
        bound_types
    }
    fn build(mut self) -> Result<TokenStream> {
        if self.items.is_empty() {
            let constructor = build_constructor(&self.self_path, &self.fields, quote!());
            return Ok(quote! { proptest::strategy::LazyJust::new(|| #constructor ) });
        }
        for item in &mut self.items {
            item.try_create_independent_strategy(&mut self.ts);
        }
        while !self.is_exists_all() {
            if !self.try_create_dependent_strategy() {
                let mut cd_str = String::new();
                let cd_idxs = self.get_cyclic_dependency().unwrap();
                for &cd_idx in &cd_idxs {
                    write!(&mut cd_str, "{} -> ", &self.items[cd_idx].key).unwrap();
                }
                write!(&mut cd_str, "{}", &self.items[cd_idxs[0]].key).unwrap();
                bail!(Span::call_site(), "found cyclic dependency. ({0})", cd_str);
            }
        }
        self.merge_all_groups();
        let s = &self.items[0].strategy_ident();
        for filter in &self.filters_fields {
            let Filter { whence, fun } = &filter.filter;
            let mut lets = Vec::new();
            for &field in &filter.vals {
                lets.push(self.items[field].let_sharp_val());
            }
            lets.push(quote!(let args = std::clone::Clone::clone(&args);));
            self.ts.extend(quote! {
                let #s = {
                    #[allow(dead_code)]
                    let args = std::clone::Clone::clone(&args);
                    proptest::strategy::Strategy::prop_filter(#s, #whence, move |_values| {
                        let args = std::ops::Deref::deref(&args);
                        #(#lets)*
                        #fun
                    })
                };
            });
        }

        let mut args = Vec::new();
        for idx in 0..self.items.len() {
            let key = self.items[idx]
                .key
                .to_valid_ident()
                .map(|ident| quote!(#ident :));
            let value = self.items[idx].expr();
            args.push(quote!(#key #value))
        }
        let constructor = build_constructor(&self.self_path, &self.fields, quote!(#(#args, )*));
        self.ts.extend(quote! {
            let #s = proptest::strategy::Strategy::prop_map(#s, |_values| #constructor);
        });
        for filter in &self.filters_self {
            self.ts.extend(filter.make_let_self(s));
        }
        let ty = parse_quote!(Self);
        for filter in &self.filters_fn {
            self.ts.extend(filter.make_let(&ty, s));
        }
        self.ts.extend(quote!(#s));
        let ts = self.ts;
        Ok(quote! { { #ts } })
    }
    fn try_create_dependent_strategy(&mut self) -> bool {
        let mut created = false;
        for idx in 0..self.items.len() {
            if self.is_exists(idx) {
                continue;
            }
            let group_next = self.items[idx]
                .dependency
                .iter()
                .map(|&idx| self.resolve_group_next_input(idx))
                .min()
                .unwrap_or(None);
            if let Some(group_next) = group_next {
                self.set_group_next(idx, group_next);
                for i in 0..self.items[idx].dependency.len() {
                    self.set_group_next(self.items[idx].dependency[i], group_next)
                }
                created = true;
            }
        }
        for idx in 0..self.items.len() {
            if let Some(group_next) = self.resolve_group_next_input(idx) {
                self.set_group_next(idx, group_next);
            }
        }
        for idx in 0..self.items.len() {
            self.register_group_dependency(idx);
        }
        for idx in 0..self.items.len() {
            if !self.is_exists(idx) {
                self.register_group_next_items(idx);
            }
        }
        for idx in 0..self.items.len() {
            if self.is_exists(idx) {
                self.register_group_next_items(idx);
            }
        }
        for idx in 0..self.items.len() {
            if self.is_group_next_new(idx) {
                let mut inputs = Vec::new();
                let mut exprs = Vec::new();
                for &input_idx in &self.items[idx].group_dependency {
                    inputs.push(self.items[input_idx].strategy_ident());
                }
                for &group_item_next in &self.items[idx].group_items_next {
                    exprs.push(self.strategy_expr(group_item_next));
                }
                let ident = self.items[idx].strategy_ident();
                self.ts.extend(quote! {
                    let #ident = {
                        #[allow(dead_code)]
                        let args = std::clone::Clone::clone(&args);
                        proptest::strategy::Strategy::prop_flat_map((#(#inputs, )*), move |_values| (#(#exprs,)*))
                    };
                });
            }
        }
        for idx in 0..self.items.len() {
            self.items[idx].group = self.items[idx].group_next;
            self.items[idx].offset = self.items[idx].offset_next.take();
            self.items[idx].group_offset = None;
            self.items[idx].group_items = take(&mut self.items[idx].group_items_next);
            self.items[idx].group_dependency.clear();
        }
        created
    }
    fn resolve_group_next_input(&self, idx: usize) -> Option<usize> {
        let item_ref = &self.items[idx];
        item_ref.group?;
        let group_next = item_ref.group_next?;
        if group_next == idx {
            return Some(idx);
        }
        self.resolve_group_next_input(group_next)
    }
    fn set_group_next(&mut self, group: usize, group_next: usize) {
        let group_next_old = self.items[group].group_next;
        if group_next_old == Some(group_next) {
            return;
        }
        if let Some(group_next_old) = group_next_old {
            if group_next_old != group {
                self.set_group_next(group_next_old, group_next)
            }
        }
        self.items[group].group_next = Some(group_next);
    }
    fn merge_all_groups(&mut self) {
        for idx in 0..self.items.len() {
            self.items[idx].group_next = Some(0);
        }
        self.merge_groups();
    }
    fn merge_groups(&mut self) {
        for idx in 0..self.items.len() {
            self.items[idx].group_next = Some(0);
        }
        for idx in 0..self.items.len() {
            self.register_group_dependency(idx);
            self.register_group_next_items(idx);
        }
        for idx in 0..self.items.len() {
            if self.is_group_next_new(idx) {
                let mut inputs = Vec::new();
                let mut exprs = Vec::new();
                for &input_idx in &self.items[idx].group_dependency {
                    inputs.push(self.items[input_idx].strategy_ident());
                }
                for &group_item_next in &self.items[idx].group_items_next {
                    let member = self.member(group_item_next);
                    exprs.push(quote!(_values.#member));
                }
                let ident = self.items[idx].strategy_ident();
                self.ts.extend( quote! {
                    let #ident = proptest::strategy::Strategy::prop_map((#(#inputs, )*), |_values| (#(#exprs,)*));
                });
            }
        }
        for idx in 0..self.items.len() {
            self.items[idx].group = self.items[idx].group_next;
            self.items[idx].offset = self.items[idx].offset_next.take();
            self.items[idx].group_offset = None;
            self.items[idx].group_items = take(&mut self.items[idx].group_items_next);
            self.items[idx].group_dependency.clear();
        }
    }
    fn register_group_dependency(&mut self, idx: usize) {
        if let Some(group_next) = self.items[idx].group_next {
            if self.is_group(idx) {
                self.items[idx].group_offset = Some(self.items[group_next].group_dependency.len());
                self.items[group_next].group_dependency.push(idx);
            }
        }
    }
    fn register_group_next_items(&mut self, idx: usize) {
        if let Some(group_next) = self.items[idx].group_next {
            debug_assert!(self.items[idx].offset_next.is_none());
            self.items[idx].offset_next = Some(self.items[group_next].group_items_next.len());
            self.items[group_next].group_items_next.push(idx);
        }
    }
    fn strategy_expr(&self, idx: usize) -> TokenStream {
        if self.is_exists(idx) {
            let member = self.member(idx);
            quote!(proptest::strategy::Just(_values.#member))
        } else {
            let item_ref = &self.items[idx];
            let mut lets = Vec::new();
            for &dep in &item_ref.dependency {
                let member = self.member(dep);
                let dep = &self.items[dep];
                let ident = &dep.key.to_dummy_ident();
                let expr = if dep.by_ref {
                    quote!(&_values.#member)
                } else {
                    quote!(std::clone::Clone::clone(&_values.#member))
                };
                lets.push(quote!(let #ident = #expr; ))
            }
            lets.push(quote! {
                #[allow(dead_code)]
                let args = std::ops::Deref::deref(&args);
            });
            let expr = &item_ref.strategy;
            quote! {
                {
                    #(#lets)*
                    #expr
                }
            }
        }
    }
    fn get_cyclic_dependency(&self) -> Option<Vec<usize>> {
        let mut results = Vec::new();
        let mut to_offset = HashMap::new();
        if self.get_cyclic_dependency_impl(0, &mut results, &mut to_offset) {
            Some(results)
        } else {
            None
        }
    }
    fn get_cyclic_dependency_impl(
        &self,
        idx: usize,
        results: &mut Vec<usize>,
        to_offset: &mut HashMap<usize, usize>,
    ) -> bool {
        if let Some(&offset) = to_offset.get(&idx) {
            results.drain(0..offset);
            return true;
        }

        to_offset.insert(idx, results.len());
        results.push(idx);
        for &dep in &self.items[idx].dependency {
            if self.get_cyclic_dependency_impl(dep, results, to_offset) {
                return true;
            }
        }
        results.pop();
        to_offset.remove(&idx);
        false
    }

    fn is_exists_all(&self) -> bool {
        (0..self.items.len()).all(|idx| self.is_exists(idx))
    }
    fn is_exists(&self, idx: usize) -> bool {
        self.items[idx].group.is_some()
    }
    fn is_group(&self, idx: usize) -> bool {
        self.items[idx].group == Some(idx)
    }
    fn is_group_next_new(&self, idx: usize) -> bool {
        let item = &self.items[idx];
        item.group_next == Some(idx) && item.group_items_next != item.group_items
    }
    fn member(&self, idx: usize) -> TokenStream {
        let item_ref = &self.items[idx];
        let member0 = idx_to_member(self.items[item_ref.group.unwrap()].group_offset.unwrap());
        let member1 = idx_to_member(item_ref.offset.unwrap());
        quote!(#member0.#member1)
    }
}

impl StrategyItem {
    fn new(
        idx: usize,
        key: FieldKey,
        by_ref: bool,
        is_any: bool,
        strategy: Expr,
        dependency: Vec<usize>,
    ) -> Self {
        Self {
            idx,
            key,
            by_ref,
            is_any,
            strategy,
            dependency,
            group: None,
            group_next: None,
            offset: None,
            offset_next: None,
            group_items: Vec::new(),
            group_items_next: Vec::new(),
            group_dependency: Vec::new(),
            group_offset: None,
        }
    }
    fn try_create_independent_strategy(&mut self, ts: &mut TokenStream) -> bool {
        if self.group.is_none() && self.dependency.is_empty() {
            let ident = self.strategy_ident();
            let expr = &self.strategy;
            ts.extend(quote!(let #ident = (#expr,);));
            self.group = Some(self.idx);
            self.group_next = self.group;
            self.offset = Some(0);
            self.offset_next = None;
            self.group_items.push(self.idx);
            true
        } else {
            false
        }
    }
    fn strategy_ident(&self) -> Ident {
        parse_str(&format!("strategy_{}", self.idx)).unwrap()
    }

    fn expr(&self) -> TokenStream {
        let member = idx_to_member(self.offset.unwrap());
        quote!(_values.#member)
    }
    fn let_sharp_val(&self) -> TokenStream {
        let expr = self.expr();
        let expr = if self.by_ref {
            quote!(&#expr)
        } else {
            quote!(std::clone::Clone::clone(&#expr))
        };
        let ident = &self.key.to_dummy_ident();
        quote!(let #ident = #expr;)
    }
}

fn idx_to_member(idx: usize) -> Member {
    let index = idx as u32;
    Member::Unnamed(Index {
        index,
        span: Span::call_site(),
    })
}
fn ident_to_member(ident: Ident) -> Member {
    let span = ident.span();
    let mut ident = to_valid_ident(&ident.unraw().to_string()).unwrap();
    ident.set_span(span);
    Member::Named(ident)
}

fn build_constructor(path: &Path, fields: &Fields, args: TokenStream) -> TokenStream {
    let args = match fields {
        Fields::Named(_) => quote! { {#args} },
        Fields::Unnamed(_) => quote! { (#args) },
        Fields::Unit => quote! {},
    };
    quote!(#path #args)
}

fn to_idxs(
    vals: &HashMap<FieldKey, Span>,
    key_to_idx: &HashMap<FieldKey, usize>,
) -> Result<Vec<usize>> {
    let mut idxs = Vec::new();
    for (key, &span) in vals {
        if let Some(&idx) = key_to_idx.get(key) {
            idxs.push(idx);
        } else {
            bail!(span, "cannot find value `#{}` in this scope.", key);
        }
    }
    idxs.sort_unstable();
    Ok(idxs)
}
