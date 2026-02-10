use crate::syn_utils::{
    impl_trait_result, span_in_args, to_valid_ident, Arg, Args, FieldKey, GenericParamSet,
    SharpVals,
};
use crate::{bound::*, syn_utils::parse_from_attrs};
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use std::collections::BTreeMap;
use std::{collections::HashMap, fmt::Write, mem::take};
use structmeta::*;
use syn::{
    parse_quote, parse_str, spanned::Spanned, Attribute, Data, DataEnum, DataStruct, DeriveInput,
    Expr, Fields, Ident, Lit, Member, Path, Result, Type,
};
use syn::{parse_quote_spanned, Meta, Pat};

pub fn derive_arbitrary(input: DeriveInput) -> Result<TokenStream> {
    let args: ArbitraryArgsForType = parse_from_attrs(&input.attrs, "arbitrary")?;
    let type_parameters = if let Some(ty) = &args.args {
        quote_spanned!(ty.span()=> type Parameters = #ty;)
    } else {
        quote! {
            type Parameters = ();
        }
    };
    let mut bounds = Bounds::from_data(args.bound);
    let expr = match &input.data {
        Data::Struct(data) => expr_for_struct(&input, data, &mut bounds)?,
        Data::Enum(data) => expr_for_enum(&input, data, &mut bounds)?,
        _ => bail!(
            input.span(),
            "`#[derive(Arbitrary)]` supports only enum and struct."
        ),
    };
    let args_var = args_var_shared();
    impl_trait_result(
        &input,
        &parse_quote!(proptest::arbitrary::Arbitrary),
        &bounds.build_wheres(quote!(proptest::arbitrary::Arbitrary + 'static)),
        quote! {
            #type_parameters
            type Strategy = proptest::strategy::BoxedStrategy<Self>;
            #[allow(clippy::redundant_closure_call)]
            #[allow(clippy::shadow_unrelated)]
            fn arbitrary_with(#args_var: <Self as proptest::arbitrary::Arbitrary>::Parameters) -> Self::Strategy {
                #[allow(dead_code)]
                fn _filter_fn<T>(f: impl Fn(&T) -> bool) -> impl Fn(&T) -> bool {
                    f
                }
                #[allow(dead_code)]
                fn _filter_fn_once<T>(f: impl FnOnce(&T) -> bool) -> impl FnOnce(&T) -> bool {
                    f
                }
                #[allow(dead_code)]
                fn _map_to_any<T: proptest::arbitrary::Arbitrary, U, F: Fn(T) -> U>(
                    _: impl Fn() -> F,
                ) -> impl proptest::strategy::Strategy<Value = T> {
                    proptest::arbitrary::any::<T>()
                }

                #[allow(dead_code)]
                fn _map_to_any_with_init<T: proptest::arbitrary::Arbitrary, U, F: Fn(T) -> U>(
                    _: impl Fn() -> F,
                    p: <T as proptest::arbitrary::Arbitrary>::Parameters,
                ) -> <T as proptest::arbitrary::Arbitrary>::Parameters {
                    p
                }

                #[allow(dead_code)]
                fn _map_to_any_with<T: proptest::arbitrary::Arbitrary, U, F: Fn(T) -> U>(
                    _: impl Fn() -> F,
                    args: <T as proptest::arbitrary::Arbitrary>::Parameters,
                ) -> impl proptest::strategy::Strategy<Value = T> {
                    proptest::arbitrary::any_with::<T>(args)
                }

                #[allow(unused_variables)]
                let #args_var = std::rc::Rc::new(#args_var);
                proptest::strategy::Strategy::boxed(#expr)
            }
        },
        args.dump.value(),
    )
}
fn expr_for_struct(
    input: &DeriveInput,
    data: &DataStruct,
    bounds: &mut Bounds,
) -> Result<TokenStream> {
    let generics = GenericParamSet::new(&input.generics);
    expr_for_fields(
        parse_quote!(Self),
        &generics,
        &data.fields,
        &input.attrs,
        true,
        bounds,
    )
}
fn expr_for_enum(input: &DeriveInput, data: &DataEnum, bounds: &mut Bounds) -> Result<TokenStream> {
    if data.variants.is_empty() {
        bail!(Span::call_site(), "zero variant enum was not supported.");
    }
    let generics = GenericParamSet::new(&input.generics);
    let mut exprs = Vec::new();
    for variant in &data.variants {
        let args: ArbitraryArgsForFieldOrVariant = parse_from_attrs(&variant.attrs, "arbitrary")?;
        let mut weight = None;
        for attr in &variant.attrs {
            let Some(ident) = attr.path().get_ident() else {
                continue;
            };
            if ident == "weight" {
                if weight.is_some() {
                    bail!(attr.span(), "`#[weight]` can specify only once.");
                }
                weight = Some(attr.parse_args::<WeightArg>()?);
            }
            if ident == "any" || ident == "strategy" || ident == "map" || ident == "by_ref" {
                bail!(
                    attr.span(),
                    "`#[{ident}]` cannot be specified for a variant. Consider specifying it for a field instead."
                );
            }
        }
        let weight = if let Some(arg) = weight {
            if arg.is_zero() {
                continue;
            } else {
                let expr = arg.0;
                quote_spanned!(expr.span()=>  _to_weight(#expr))
            }
        } else {
            quote!(1)
        };
        let variant_ident = &variant.ident;
        let mut bounds = bounds.child(args.bound);
        let expr = expr_for_fields(
            parse_quote!(Self::#variant_ident),
            &generics,
            &variant.fields,
            &variant.attrs,
            false,
            &mut bounds,
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
    bounds: &mut Bounds,
) -> Result<TokenStream> {
    let b = StrategyBuilder::from_fields(self_path, fields, attrs, filter_allow_fn)?;
    b.get_bound_types(generics, bounds)?;
    b.build()
}

#[derive(StructMeta)]
struct WeightArg(Expr);
impl WeightArg {
    fn is_zero(&self) -> bool {
        if let Expr::Lit(lit) = &self.0 {
            if let Lit::Int(lit) = &lit.lit {
                if let Ok(value) = lit.base10_parse::<u32>() {
                    return value == 0;
                }
            }
        }
        false
    }
}

#[derive(StructMeta)]
struct AnyArgs {
    #[struct_meta(unnamed)]
    initializer: Option<Expr>,
    setters: HashMap<String, NameValue<Expr>>,
}
impl Default for AnyArgs {
    fn default() -> Self {
        Self::empty()
    }
}

impl AnyArgs {
    fn empty() -> Self {
        Self {
            initializer: None,
            setters: HashMap::new(),
        }
    }
    fn into_strategy(self, ty: &StrategyValueType) -> TokenStream {
        if self.initializer.is_none() && self.setters.is_empty() {
            ty.any()
        } else {
            let init = self
                .initializer
                .unwrap_or_else(|| parse_quote!(std::default::Default::default()))
                .to_token_stream();
            if self.setters.is_empty() {
                ty.any_with(init)
            } else {
                let mut setters: Vec<_> = self.setters.into_iter().collect();
                setters.sort_by(|v0, v1| v0.0.cmp(&v1.0));
                let setters = setters.into_iter().map(|(name, expr)| {
                    let member = Member::Named(to_valid_ident(&name).unwrap());
                    let expr = &expr.value;
                    quote!(_any_args.#member = #expr;)
                });
                let any_with = ty.any_with(quote!(_any_args));
                let any_with_args_let = ty.any_with_args_let(quote!(_any_args), init);
                quote! {
                    {
                        #any_with_args_let;
                        #(#setters)*
                        #any_with
                    }
                }
            }
        }
    }
}

#[derive(StructMeta, Default)]
struct ArbitraryArgsForType {
    args: Option<Type>,
    bound: Option<Vec<Bound>>,
    dump: Flag,
}

#[derive(StructMeta, Default)]
struct ArbitraryArgsForFieldOrVariant {
    bound: Option<Vec<Bound>>,
}

#[derive(Clone)]
struct Filter {
    whence: Expr,
    expr: Expr,
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
        let expr;
        match values.len() {
            1 => {
                let mut iter = values.into_iter();
                expr = iter.next().unwrap();
                let whence_str = expr.to_token_stream().to_string();
                whence = parse_quote!(#whence_str);
            }
            2 => {
                let mut iter = values.into_iter();
                whence = iter.next().unwrap();
                expr = iter.next().unwrap();
            }
            _ => bail!(
                span,
                "expected `#[filter(whence, fun)]` or `#[filter(fun)]`."
            ),
        }
        Ok(Self { whence, expr })
    }
    fn from_enum_attrs_make_let(attrs: &[Attribute], var: &Ident) -> Result<TokenStream> {
        let mut results = TokenStream::new();
        for attr in attrs {
            if attr.path().is_ident("filter") {
                let mut sharp_vals = SharpVals::new(false, true);
                let mut filter = Filter::parse(attr.span(), sharp_vals.expand_args(&attr.meta)?)?;
                if sharp_vals.self_span.is_none() {
                    filter = filter.with_fn_arg_self();
                }
                let self_in_expr = quote_spanned!(attr.span()=> _self);
                results.extend(filter.make_let_as_expr(var, &self_in_expr, &quote!()));
            }
        }
        Ok(results)
    }
    fn with_fn_arg(&self, arg: &Ident, arg_by_ref: bool, arg_ty: &Type) -> Self {
        let span = self.expr.span();
        let expr = &self.expr;
        let arg = if arg_by_ref {
            quote!(#arg)
        } else {
            quote!(&#arg)
        };
        let expr = parse_quote_spanned!(span=> (_filter_fn_once::<#arg_ty>(#expr))(#arg));
        Self {
            expr,
            whence: self.whence.clone(),
        }
    }
    fn with_fn_arg_self(&self) -> Self {
        self.with_fn_arg(
            &parse_quote_spanned! (self.span()=> _self),
            true,
            &parse_quote!(Self),
        )
    }

    fn make_let_as_expr(
        &self,
        var: &Ident,
        params: &TokenStream,
        lets: &TokenStream,
    ) -> TokenStream {
        let expr = self.expr.to_token_stream();
        Self::make_let_with(var, &self.whence, params, lets, expr)
    }
    fn make_let_as_fn(&self, var: &Ident, arg_ty: &Type) -> TokenStream {
        let span = self.expr.span();
        let expr = &self.expr;
        let fun = parse_quote_spanned!(span=> _filter_fn::<#arg_ty>(#expr));
        Self::make_let_with_fun(var, &self.whence, fun)
    }

    fn make_let_with(
        var: &Ident,
        whence: &Expr,
        params: &TokenStream,
        lets: &TokenStream,
        expr: TokenStream,
    ) -> TokenStream {
        let fun = quote_spanned! {expr.span()=> move |#params| {
            #lets
            #expr
        }};
        Self::make_let_with_fun(var, whence, fun)
    }
    fn make_let_with_fun(var: &Ident, whence: &Expr, fun: TokenStream) -> TokenStream {
        let args = args_var_shared();
        let args_in_expr = args_var(fun.span());
        quote_spanned! {fun.span()=>
            let #var = {
                #[allow(unused_variables)]
                let #args_in_expr = <std::rc::Rc<_> as std::clone::Clone>::clone(&#args);
                proptest::strategy::Strategy::prop_filter(#var, #whence, #fun)
            };
        }
    }
    fn span(&self) -> Span {
        self.expr.span()
    }
}

#[derive(Clone)]
struct UnaryFilter {
    filter: Filter,
    arg_exists: bool,
    arg: Ident,
    arg_by_ref: bool,
    arg_ty: Type,
}
impl UnaryFilter {
    fn make_let_expr(&self, var: &Ident, ps: &TokenStream, lets: &TokenStream) -> TokenStream {
        self.to_expr_filter().make_let_as_expr(var, ps, lets)
    }
    fn make_let_fn(&self, var: &Ident) -> TokenStream {
        if self.arg_exists {
            let arg = &self.arg;
            let arg_ty = &self.arg_ty;
            let lets = if self.arg_by_ref {
                quote!()
            } else {
                quote!(let #arg = <#arg_ty as std::clone::Clone>::clone(#arg);)
            };
            self.filter.make_let_as_expr(var, &quote!(#arg), &lets)
        } else {
            self.filter.make_let_as_fn(var, &self.arg_ty)
        }
    }
    fn to_expr_filter(&self) -> Filter {
        if self.arg_exists {
            self.filter.clone()
        } else {
            self.filter
                .with_fn_arg(&self.arg, self.arg_by_ref, &self.arg_ty)
        }
    }
}

struct FieldsFilter {
    filter: Filter,
    _vals: Vec<usize>,
}

struct StrategyBuilder {
    ts: TokenStream,
    items: Vec<StrategyItem>,
    self_path: Path,
    fields: Fields,
    filters_fields: Vec<FieldsFilter>,
    filters_self: Vec<Filter>,
}

impl StrategyBuilder {
    fn from_fields(
        self_path: Path,
        fields: &Fields,
        attrs: &[Attribute],
        filter_allow_self: bool,
    ) -> Result<Self> {
        let mut ts = TokenStream::new();
        let mut fs = Vec::new();
        let mut by_refs = Vec::new();
        let mut key_to_idx = HashMap::new();
        for (idx, field) in fields.iter().enumerate() {
            key_to_idx.insert(FieldKey::from_field(idx, field), idx);
            fs.push(field);
            let mut by_ref = false;
            for attr in &field.attrs {
                if attr.path().is_ident("by_ref") {
                    by_ref = true;
                    match &attr.meta {
                        Meta::Path(_) => {}
                        _ => {
                            let span = span_in_args(&attr.meta);
                            bail!(span, "Arguments are not allowed.");
                        }
                    }
                }
            }
            by_refs.push(by_ref);
        }
        let mut items_field = Vec::new();
        let mut items_other = Vec::new();
        let mut filters_fields = Vec::new();

        for (idx, field) in fields.iter().enumerate() {
            let key = FieldKey::from_field(idx, field);
            let mut expr_strategy = None::<StrategyExpr>;
            let mut expr_map = None::<StrategyExpr>;
            let mut filters_field = Vec::new();
            let mut sharp_vals_strategy = SharpVals::new(true, false);
            let mut sharp_vals_map = SharpVals::new(true, false);
            let by_ref = by_refs[idx];
            let mut is_any = false;
            let mut strategy_value_type = StrategyValueType::Type(field.ty.clone());
            for attr in &field.attrs {
                if attr.path().is_ident("map") {
                    if expr_map.is_some() {
                        bail!(attr.span(), "`#[map]` can be specified only once.");
                    }
                    let args: Args = sharp_vals_map.expand_args_or_default(&attr.meta)?;
                    let expr = args.expect_single_value(attr.span())?;
                    let ty = &field.ty;
                    let input = key.to_dummy_ident();
                    expr_map = Some(StrategyExpr::new(
                        expr.span(),
                        quote_spanned!(expr.span()=> #ty),
                        quote_spanned!(expr.span()=> (#expr)(#input)),
                        true,
                    ));
                    if let Some(ty) = input_type(expr) {
                        strategy_value_type = StrategyValueType::Type(ty.clone());
                    } else {
                        let dependency_map = to_idxs(&sharp_vals_map.vals, &key_to_idx)?;
                        let mut lets = Vec::new();
                        for idx in dependency_map {
                            let field = &fs[idx];
                            let key = FieldKey::from_field(idx, field);
                            let ident = key.to_dummy_ident();
                            let ty = &field.ty;
                            let ty = if by_refs[idx] {
                                quote!(&#ty)
                            } else {
                                quote!(#ty)
                            };
                            lets.push(quote!(let #ident : #ty = unreachable!();))
                        }
                        strategy_value_type = StrategyValueType::Map(quote! { || {
                            #[allow(clippy::diverging_sub_expression)]
                            #[allow(unreachable_code)]
                            {
                                #(#lets)*
                                #expr
                            }
                        }});
                    }
                }
            }
            for attr in &field.attrs {
                let is_strategy_attr = attr.path().is_ident("strategy");
                let is_any_attr = attr.path().is_ident("any");
                if expr_strategy.is_some() && (is_strategy_attr || is_any_attr) {
                    bail!(
                        attr.span(),
                        "`#[any]` and `#[strategy]` can only be specified once in total."
                    );
                }
                if is_strategy_attr {
                    let args: Args = sharp_vals_strategy.expand_args_or_default(&attr.meta)?;
                    let expr = args.expect_single_value(attr.span())?;
                    let ty = strategy_value_type.get();
                    let func_ident = Ident::new(&format!("_strategy_of_{key}"), expr.span());
                    ts.extend(quote_spanned! {ty.span()=>
                        #[allow(dead_code)]
                        #[allow(non_snake_case)]
                        fn #func_ident<T: std::fmt::Debug, S: proptest::strategy::Strategy<Value = T>>(s: S) -> impl proptest::strategy::Strategy<Value = T> { s }
                    });
                    let args = args_var_shared();
                    let args_in_expr = args_var(expr.span());
                    expr_strategy = Some(StrategyExpr::new(
                        expr.span(),
                        quote!(_),
                        quote_spanned!(expr.span()=> #func_ident::<#ty, _>(
                        {
                            #[allow(unused_variables)]
                            let #args_in_expr = std::ops::Deref::deref(&#args);
                            #expr
                        })),
                        false,
                    ));
                }
                if is_any_attr {
                    is_any = true;
                    let any_attr: AnyArgs =
                        sharp_vals_strategy.expand_args_or_default(&attr.meta)?;
                    expr_strategy = Some(StrategyExpr::new(
                        attr.span(),
                        quote!(),
                        any_attr.into_strategy(&strategy_value_type),
                        false,
                    ));
                }
            }
            for attr in &field.attrs {
                if attr.path().is_ident("filter") {
                    let mut sharp_vals = SharpVals::new(true, false);
                    let filter = Filter::parse(attr.span(), sharp_vals.expand_args(&attr.meta)?)?;
                    let arg = key.to_dummy_ident();
                    let uf = UnaryFilter {
                        filter,
                        arg_exists: sharp_vals.vals.contains_key(&key),
                        arg_by_ref: by_ref,
                        arg_ty: field.ty.clone(),
                        arg,
                    };
                    if sharp_vals.vals.is_empty() || (uf.arg_exists && sharp_vals.vals.len() == 1) {
                        filters_field.push(uf);
                    } else {
                        let mut vals = to_idxs(&sharp_vals.vals, &key_to_idx)?;
                        if !uf.arg_exists {
                            vals.push(idx);
                            vals.sort_unstable();
                        }
                        let filter = uf.to_expr_filter();
                        filters_fields.push(FieldsFilter {
                            filter,
                            _vals: vals,
                        });
                    }
                }
            }
            let mut expr_strategy = if let Some(expr_strategy) = expr_strategy {
                expr_strategy
            } else {
                is_any = true;
                let ty = strategy_value_type.get();
                StrategyExpr::new(
                    field.span(),
                    quote!(#ty),
                    AnyArgs::empty().into_strategy(&strategy_value_type),
                    false,
                )
            };
            let dependency_strategy = to_idxs(&sharp_vals_strategy.vals, &key_to_idx)?;
            let arbitrary_type = if is_any {
                if let StrategyValueType::Type(ty) = strategy_value_type {
                    Some(ty)
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(mut expr_map) = expr_map {
                let base_idx = fields.len() + items_other.len();
                let mut dependency_map = to_idxs(&sharp_vals_map.vals, &key_to_idx)?;
                dependency_map.push(base_idx);
                expr_map.filters = filters_field;
                items_field.push(StrategyItem::new(
                    idx,
                    key.clone(),
                    by_ref,
                    true,
                    Some(base_idx),
                    arbitrary_type,
                    expr_map,
                    dependency_map,
                ));
                items_other.push(StrategyItem::new(
                    base_idx,
                    key,
                    false,
                    false,
                    None,
                    None,
                    expr_strategy,
                    dependency_strategy,
                ));
            } else {
                expr_strategy.filters = filters_field;
                items_field.push(StrategyItem::new(
                    idx,
                    key,
                    by_ref,
                    true,
                    None,
                    arbitrary_type,
                    expr_strategy,
                    dependency_strategy,
                ));
            }
        }
        let mut filters_self = Vec::new();
        for attr in attrs {
            if attr.path().is_ident("filter") {
                let mut sharp_vals = SharpVals::new(true, filter_allow_self);
                let mut filter = Filter::parse(attr.span(), sharp_vals.expand_args(&attr.meta)?)?;
                if !sharp_vals.vals.is_empty() {
                    let vals = to_idxs(&sharp_vals.vals, &key_to_idx)?;
                    filters_fields.push(FieldsFilter {
                        filter,
                        _vals: vals,
                    });
                } else if filter_allow_self {
                    if sharp_vals.self_span.is_none() {
                        filter = filter.with_fn_arg_self();
                    }
                    filters_self.push(filter);
                } else {
                    let span = span_in_args(&attr.meta);
                    bail!(span, "Filters that reference `self` in the variant (filters with no reference to the field) cannot be set.")
                }
            }
        }
        let fields = fields.clone();
        items_field.extend(items_other);
        Ok(Self {
            ts,
            items: items_field,
            self_path,
            fields,
            filters_fields,
            filters_self,
        })
    }
    fn get_bound_types(&self, generics: &GenericParamSet, bounds: &mut Bounds) -> Result<()> {
        if !bounds.can_extend {
            return Ok(());
        }
        for (idx, field) in self.fields.iter().enumerate() {
            let args: ArbitraryArgsForFieldOrVariant = parse_from_attrs(&field.attrs, "arbitrary")?;
            let mut bounds = bounds.child(args.bound);
            if bounds.can_extend {
                if let Some(ty) = &self.items[idx].arbitrary_type {
                    if generics.contains_in_type(ty) {
                        bounds.ty.push(ty.clone());
                    }
                }
            }
        }
        Ok(())
    }
    fn build(mut self) -> Result<TokenStream> {
        if self.items.is_empty() {
            let constructor = build_constructor(&self.self_path, &self.fields, quote!());
            return Ok(quote! { proptest::strategy::LazyJust::new(|| #constructor ) });
        }
        for item in &mut self.items {
            item.try_create_independent_strategy(&mut self.ts);
        }
        while !self.is_exists_all_fields() {
            if !self.try_create_dependent_strategy() {
                let mut cd_str = String::new();
                let cd_idxs = self.get_cyclic_dependency().unwrap();
                for &cd_idx in &cd_idxs {
                    let item = &self.items[cd_idx];
                    if item.is_field {
                        write!(&mut cd_str, "{} -> ", &item.key).unwrap();
                    }
                }
                for &cd_idx in &cd_idxs {
                    let item = &self.items[cd_idx];
                    if item.is_field {
                        write!(&mut cd_str, "{}", &item.key).unwrap();
                        break;
                    }
                }
                bail!(Span::call_site(), "found cyclic dependency. ({0})", cd_str);
            }
        }
        self.merge_all_groups();
        let var = &self.items[0].strategy_ident();
        let ps = self.pat_group_vars(0);
        for filter in &self.filters_fields {
            let lets = self.let_group_vars(0, true);
            self.ts
                .extend(filter.filter.make_let_as_expr(var, &ps, &lets));
        }

        let mut args = Vec::new();
        for idx in 0..self.fields.len() {
            let key = &self.items[idx].key;
            let value = key.to_dummy_ident();
            args.push(if let Some(key) = key.to_valid_ident() {
                quote!(#key : #value)
            } else {
                quote!(#value)
            });
        }
        let constructor = build_constructor(&self.self_path, &self.fields, quote!(#(#args, )*));
        self.ts.extend(quote! {
            let #var = proptest::strategy::Strategy::prop_map(#var, |#ps| #constructor);
        });
        for filter in &self.filters_self {
            let self_in_expr = parse_quote_spanned!(filter.span()=> _self);
            self.ts
                .extend(filter.make_let_as_expr(var, &self_in_expr, &quote!()));
        }
        self.ts.extend(quote!(#var));
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
                .min() // None if any item is ungenerated; otherwise use the smallest item as the new group.
                .unwrap_or(None);
            if let Some(group_next) = group_next {
                // Set this item's group and merge dependent groups into one.
                self.set_group_next_new(idx, group_next);
                created = true;
            }
        }
        self.normalize_group_nexts();
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
                let mut ps = Vec::new();
                let mut exprs = Vec::new();
                for &input_idx in &self.items[idx].group_dependency {
                    inputs.push(self.items[input_idx].strategy_ident());
                    ps.push(self.pat_group_vars(input_idx));
                }
                let inputs = cons_tuple(&inputs);
                let ps = cons_tuple(&ps);
                let ps_next = self.pat_group_next_vars(idx);
                let var = Ident::new("_s", Span::call_site());
                let lets = self.let_group_vars(idx, true);
                let mut filter_lets = TokenStream::new();
                for &group_item_next in &self.items[idx].group_items_next {
                    let mut expr = self.strategy_expr(group_item_next);
                    for filter in &expr.filters {
                        filter_lets.extend(filter.make_let_expr(&var, &ps_next, &lets));
                    }
                    expr.filters.clear();
                    exprs.push(expr);
                }
                let ident = self.items[idx].strategy_ident();
                let args = args_var_shared();
                let exprs = if exprs.iter().all(|e| e.is_jast) {
                    let exprs: Vec<_> = exprs.iter().map(|e| &e.expr).collect();
                    let exprs = cons_tuple(&exprs);
                    quote! {
                        {
                            let #var = proptest::strategy::Strategy::prop_map((#inputs), {
                                #[allow(unused_variables)]
                                let #args = <std::rc::Rc<_> as std::clone::Clone>::clone(&#args);
                                move |#ps| #exprs
                            });
                            #filter_lets
                            #var
                        }
                    }
                } else {
                    let exprs = cons_tuple(&exprs);
                    quote! {
                        {
                            let #var = proptest::strategy::Strategy::prop_flat_map(#inputs, {
                                #[allow(unused_variables)]
                                let #args = <std::rc::Rc<_> as std::clone::Clone>::clone(&#args);
                                move |#ps| #exprs
                            });
                            #filter_lets
                            #var
                        }
                    }
                };
                let args = args_var_shared();
                self.ts.extend(quote! {
                    let #ident = {
                        #[allow(unused_variables)]
                        let #args = <std::rc::Rc<_> as std::clone::Clone>::clone(&#args);
                        #exprs
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

    fn normalize_group_nexts(&mut self) {
        for idx in 0..self.items.len() {
            if let Some(group_next) = self.resolve_group_next(idx) {
                self.set_group_next(idx, group_next);
            }
        }
    }

    /// Return which group's input this item becomes in the next stage.
    ///
    /// None if the item is not generated, because it does not appear as a group input.
    fn resolve_group_next_input(&self, idx: usize) -> Option<usize> {
        let item_ref = &self.items[idx];
        item_ref.group?;
        self.resolve_group_next(item_ref.group_next?)
    }
    fn resolve_group_next(&self, idx: usize) -> Option<usize> {
        let mut idx = self.items[idx].group_next?;
        while self.items[idx].group_next != Some(idx) {
            idx = self.items[idx].group_next.unwrap();
        }
        Some(idx)
    }
    fn set_group_next_new(&mut self, idx: usize, group_next: usize) {
        if let Some(base_idx) = self.items[idx].base_idx {
            self.items[base_idx].is_dropped = true;
        }
        self.set_group_next(idx, group_next);
        for i in 0..self.items[idx].dependency.len() {
            self.set_group_next(self.items[idx].dependency[i], group_next);
        }
    }

    fn set_group_next(&mut self, group: usize, group_next: usize) {
        let group_next_old = self.items[group].group_next;
        if group_next_old == Some(group_next) {
            return;
        }
        if let Some(group_next_old) = group_next_old {
            if group_next_old != group {
                self.set_group_next(group_next_old, group_next);
            }
        }
        self.items[group].group_next = Some(group_next)
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
                let mut ps = Vec::new();
                let mut exprs = Vec::new();
                for &input_idx in &self.items[idx].group_dependency {
                    inputs.push(self.items[input_idx].strategy_ident());
                    ps.push(self.pat_group_vars(input_idx));
                }
                for &group_item_next in &self.items[idx].group_items_next {
                    exprs.push(self.items[group_item_next].key.to_dummy_ident());
                }
                let var = self.items[idx].strategy_ident();
                let inputs = cons_tuple(&inputs);
                let ps = cons_tuple(&ps);
                let exprs = cons_tuple(&exprs);
                self.ts.extend(quote! {
                    let #var = proptest::strategy::Strategy::prop_map(#inputs, |#ps| #exprs);
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
        let item = &self.items[idx];
        if !item.is_dropped {
            if let Some(group_next) = item.group_next {
                debug_assert!(item.offset_next.is_none());
                self.items[idx].offset_next = Some(self.items[group_next].group_items_next.len());
                self.items[group_next].group_items_next.push(idx);
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

    fn is_exists_all_fields(&self) -> bool {
        (0..self.fields.len()).all(|idx| self.is_exists(idx))
    }
    fn is_exists(&self, idx: usize) -> bool {
        let item = &self.items[idx];
        item.group.is_some() || item.is_dropped
    }
    fn is_group(&self, idx: usize) -> bool {
        self.items[idx].group == Some(idx)
    }
    fn is_group_next(&self, idx: usize) -> bool {
        self.items[idx].group_next == Some(idx)
    }
    fn is_group_next_new(&self, idx: usize) -> bool {
        let item = &self.items[idx];
        item.group_next == Some(idx) && item.group_items_next != item.group_items
    }
    fn pat_group_vars(&self, idx: usize) -> TokenStream {
        assert!(self.is_group(idx));
        let mut ps = Vec::new();
        for &idx in &self.items[idx].group_items {
            ps.push(self.items[idx].key.to_dummy_ident());
        }
        cons_tuple(&ps)
    }
    fn pat_group_next_vars(&self, idx: usize) -> TokenStream {
        assert!(self.is_group_next(idx));
        let mut ps = Vec::new();
        for &idx in &self.items[idx].group_items_next {
            ps.push(self.items[idx].key.to_dummy_ident());
        }
        cons_tuple(&ps)
    }
    fn let_group_vars(&self, idx: usize, from_ref: bool) -> TokenStream {
        let mut lets = Vec::new();
        for &idx in &self.items[idx].group_items {
            lets.push(self.items[idx].let_sharp_val(from_ref));
        }
        quote!(#(#lets)*)
    }
    fn strategy_expr(&self, idx: usize) -> StrategyExpr {
        if self.is_exists(idx) {
            let ident = self.items[idx].key.to_dummy_ident();
            StrategyExpr::new(
                ident.span(),
                quote!(_),
                quote!(std::clone::Clone::clone(&#ident)),
                true,
            )
        } else {
            let item = &self.items[idx];
            let mut lets = Vec::new();
            for &dep in &item.dependency {
                lets.push(self.items[dep].let_sharp_val(false));
            }
            let expr = &item.expr.expr;
            let args = args_var_shared();
            let args_in_expr = args_var(item.expr.span);
            lets.push(quote! {
                #[allow(unused_variables)]
                let #args_in_expr = std::ops::Deref::deref(&#args);
            });
            StrategyExpr {
                span: item.expr.span,
                expr: quote! {
                    {
                        #(#lets)*
                        #expr
                    }
                },
                filters: item.expr.filters.clone(),
                ty: item.expr.ty.clone(),
                is_jast: item.expr.is_jast,
            }
        }
    }
}

struct StrategyItem {
    idx: usize,
    key: FieldKey,
    by_ref: bool,
    is_field: bool,

    /// Indexes of temporary strategies this item depends on; temporary strategies do not appear in the final field strategy.
    base_idx: Option<usize>,
    arbitrary_type: Option<Type>,
    expr: StrategyExpr,

    /// Indexes of dependent items.
    dependency: Vec<usize>,

    /// True if this item is dropped; only temporary strategies are dropped.
    is_dropped: bool,

    /// Group this item belongs to; None if its strategy has not been generated.
    group: Option<usize>,

    /// Group this item belongs to in the next stage.
    /// If the target group belongs to another group, this item also belongs to that other group.
    group_next: Option<usize>,

    /// Position within the item's group.
    offset: Option<usize>,

    /// Index within the group this item belongs to in the next stage.
    offset_next: Option<usize>,

    /// If this item is a group, indexes of items in the group.
    group_items: Vec<usize>,
    /// If this item is a group in the next stage, indexes of items in the group at that stage.
    group_items_next: Vec<usize>,
    /// If this item is a group, indexes of groups it depends on.
    group_dependency: Vec<usize>,
    /// If this item is a group, its position in the next stage's `group_dependency`.
    group_offset: Option<usize>,
}

impl StrategyItem {
    #[allow(clippy::too_many_arguments)]
    fn new(
        idx: usize,
        key: FieldKey,
        by_ref: bool,
        is_field: bool,
        base_idx: Option<usize>,
        arbitrary_type: Option<Type>,
        expr: StrategyExpr,
        dependency: Vec<usize>,
    ) -> Self {
        Self {
            idx,
            key,
            by_ref,
            is_field,
            base_idx,
            arbitrary_type,
            expr,
            dependency,
            is_dropped: false,
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
            let expr = &self.expr;
            let args = args_var_shared();
            let args_in_expr = args_var(expr.span);
            ts.extend(quote_spanned! {expr.span=>
                let #ident = {
                    #[allow(unused_variables)]
                    let #args_in_expr = std::ops::Deref::deref(&#args);
                    #expr
                };
            });
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
    fn let_sharp_val(&self, from_ref: bool) -> TokenStream {
        let ident = self.key.to_dummy_ident();
        let expr = if from_ref {
            quote!(#ident)
        } else {
            quote!(&#ident)
        };
        let expr = if self.by_ref {
            expr
        } else {
            quote!(std::clone::Clone::clone(#expr))
        };
        quote!(let #ident = #expr;)
    }
}

enum StrategyValueType {
    Type(Type),
    Map(TokenStream),
}
impl StrategyValueType {
    fn get(&self) -> Type {
        match self {
            StrategyValueType::Type(ty) => ty.clone(),
            StrategyValueType::Map(_) => parse_quote!(_),
        }
    }
    fn any(&self) -> TokenStream {
        match self {
            StrategyValueType::Type(ty) => quote!(proptest::arbitrary::any::<#ty>()),
            StrategyValueType::Map(expr) => quote!(_map_to_any(#expr)),
        }
    }
    fn any_with_args_let(&self, var: TokenStream, init: TokenStream) -> TokenStream {
        match self {
            StrategyValueType::Type(ty) => {
                quote!(let mut #var :<#ty as proptest::arbitrary::Arbitrary>::Parameters = #init;)
            }
            StrategyValueType::Map(expr) => {
                quote!(let mut #var = _map_to_any_with_init(#expr, #init);)
            }
        }
    }
    fn any_with(&self, args: TokenStream) -> TokenStream {
        match self {
            StrategyValueType::Type(ty) => quote!(proptest::arbitrary::any_with::<#ty>(#args)),
            StrategyValueType::Map(expr) => quote!(_map_to_any_with(#expr, #args)),
        }
    }
}
struct StrategyExpr {
    span: Span,
    expr: TokenStream,
    filters: Vec<UnaryFilter>,
    ty: TokenStream,
    is_jast: bool,
}
impl StrategyExpr {
    fn new(span: Span, ty: TokenStream, expr: TokenStream, is_jast: bool) -> Self {
        Self {
            span,
            ty,
            expr,
            is_jast,
            filters: Vec::new(),
        }
    }
}
impl ToTokens for StrategyExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let expr = &self.expr;
        let expr = if self.is_jast {
            let ty = &self.ty;
            quote!(proptest::strategy::Just::<#ty>(#expr))
        } else {
            quote!(#expr)
        };
        let expr = if self.filters.is_empty() {
            expr
        } else {
            let mut filter_lets = Vec::new();
            let var: Ident = parse_quote! { _s };
            for filter in &self.filters {
                filter_lets.push(filter.make_let_fn(&var));
            }
            quote! {
                {
                    let #var = #expr;
                    #(#filter_lets)*
                    #var
                }
            }
        };
        tokens.extend(expr);
    }
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
    vals: &BTreeMap<FieldKey, Span>,
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

fn input_type(expr: &Expr) -> Option<&Type> {
    if let Expr::Closure(closure) = expr {
        let inputs = &closure.inputs;
        if inputs.len() == 1 {
            if let Pat::Type(t) = &inputs[0] {
                return Some(&t.ty);
            }
        }
    }
    None
}

fn cons_tuple(es: &[impl ToTokens]) -> TokenStream {
    match es {
        [] => quote!(()),
        [e0] => quote!(#e0),
        [e0, e1] => quote!((#e0, #e1)),
        [e0, el @ ..] => {
            let el = cons_tuple(el);
            quote!((#e0, #el))
        }
    }
}

fn args_var_shared() -> Ident {
    Ident::new("args_shared", Span::call_site())
}
fn args_var(span: Span) -> Ident {
    Ident::new("args", span)
}
