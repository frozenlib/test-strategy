use std::mem::replace;

use crate::syn_utils::{Arg, Args};
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    parse2, parse_quote, parse_str, spanned::Spanned, token, Attribute, Block, Expr, Field,
    FieldMutability, FnArg, Ident, ItemFn, LitStr, Pat, Result, ReturnType, Visibility,
};

// Check whether given attribute is a test attribute of forms:
// * `#[test]`
// * `#[core::prelude::*::test]` or `#[::core::prelude::*::test]`
// * `#[std::prelude::*::test]` or `#[::std::prelude::*::test]`
fn is_test_attribute(attr: &Attribute) -> bool {
    let path = match &attr.meta {
        syn::Meta::Path(path) => path,
        _ => return false,
    };
    const CANDIDATES_LEN: usize = 4;

    let candidates: [[&str; CANDIDATES_LEN]; 2] = [
        ["core", "prelude", "*", "test"],
        ["std", "prelude", "*", "test"],
    ];
    if path.leading_colon.is_none()
        && path.segments.len() == 1
        && path.segments[0].arguments.is_none()
        && path.segments[0].ident == "test"
    {
        return true;
    } else if path.segments.len() != candidates[0].len() {
        return false;
    }
    candidates.into_iter().any(|segments| {
        path.segments.iter().zip(segments).all(|(segment, path)| {
            segment.arguments.is_none() && (path == "*" || segment.ident == path)
        })
    })
}

pub fn build_proptest(attr: TokenStream, mut item_fn: ItemFn) -> Result<TokenStream> {
    let mut attr_args = None;
    if !attr.is_empty() {
        attr_args = Some(parse2::<Args>(attr)?);
    }
    let mut dump = false;
    item_fn.attrs.retain(|attr| {
        if attr.path().is_ident("proptest_dump") {
            dump = true;
            false
        } else {
            true
        }
    });
    let (mut attr_args, config_args) = TestFnAttrArgs::from(attr_args.unwrap_or_default())?;
    dump |= attr_args.dump;
    let args_type_str = format!("_{}Args", to_camel_case(&item_fn.sig.ident.to_string()));
    let args_type_ident: Ident = parse_str(&args_type_str).unwrap();
    let args = item_fn
        .sig
        .inputs
        .iter()
        .map(TestFnArg::from)
        .collect::<Result<Vec<_>>>()?;
    let args_pats = args.iter().map(|arg| arg.pat());
    let block = &item_fn.block;
    if item_fn.sig.asyncness.is_none() {
        attr_args.r#async = None;
    }
    let output = replace(&mut item_fn.sig.output, ReturnType::Default);
    let block = if let Some(a) = attr_args.r#async {
        item_fn.sig.asyncness = None;
        a.apply(block, output)
    } else {
        match output {
            ReturnType::Default => quote!(#block),
            ReturnType::Type(_, ty) => {
                let f = Ident::new("__test_body", Span::mixed_site());
                quote!({
                    let #f = move || -> #ty {
                        #block
                    };
                    ::std::result::Result::map_err(#f(),
                        |e| ::proptest::test_runner::TestCaseError::fail(::std::string::ToString::to_string(&e)))?;
                })
            }
        }
    };
    let block = quote! {
        {
            let #args_type_ident { #(#args_pats,)* } = input;
            #block
        }
    };
    item_fn.sig.inputs = parse_quote! { input: #args_type_ident };
    item_fn.block = Box::new(parse2(block)?);
    if !item_fn.attrs.iter().any(is_test_attribute) {
        let test_attr: Attribute = parse_quote! {
            #[::core::prelude::v1::test]
        };
        item_fn.attrs.push(test_attr);
    }
    let args_fields = args.iter().map(|arg| &arg.field);
    let config = to_proptest_config(config_args);
    let ts = quote! {
        #[cfg(test)]
        #[derive(test_strategy::Arbitrary, Debug)]
        struct #args_type_ident {
            #(#args_fields,)*
        }
        #[cfg(test)]
        proptest::proptest! {
            #config
            #item_fn
        }
    };
    if dump {
        panic!("{}", ts);
    }
    Ok(ts)
}

fn to_proptest_config(args: Args) -> TokenStream {
    if args.is_empty() {
        return quote!();
    }
    let mut base_expr = None;
    let mut inits = Vec::new();
    for arg in args {
        match arg {
            Arg::Value(value) => base_expr = Some(value),
            Arg::NameValue { name, value, .. } => inits.push(quote!(#name : #value)),
        }
    }
    let base_expr = base_expr.unwrap_or_else(|| {
        parse_quote!(<proptest::test_runner::Config as std::default::Default>::default())
    });
    quote! {
        #![proptest_config(proptest::test_runner::Config {
            #(#inits,)*
            .. #base_expr
          })]
    }
}
struct TestFnArg {
    field: Field,
    mutability: Option<token::Mut>,
}
impl TestFnArg {
    fn from(arg: &FnArg) -> Result<Self> {
        if let FnArg::Typed(arg) = arg {
            if let Pat::Ident(ident) = arg.pat.as_ref() {
                if ident.attrs.is_empty() && ident.by_ref.is_none() && ident.subpat.is_none() {
                    return Ok(Self {
                        field: Field {
                            attrs: arg.attrs.clone(),
                            vis: Visibility::Inherited,
                            mutability: FieldMutability::None,
                            ident: Some(ident.ident.clone()),
                            colon_token: Some(arg.colon_token),
                            ty: arg.ty.as_ref().clone(),
                        },
                        mutability: ident.mutability,
                    });
                }
            } else {
                bail!(arg.pat.span(), "argument pattern not supported.");
            }
        }
        bail!(
            arg.span(),
            "argument {} is not supported.",
            arg.to_token_stream()
        );
    }
    fn pat(&self) -> TokenStream {
        let mutability = &self.mutability;
        let ident = &self.field.ident;
        quote!(#mutability #ident)
    }
}

#[derive(Debug, Clone)]
enum Async {
    Tokio,
    Expr(Expr),
}
impl Async {
    fn apply(&self, block: &Block, output: ReturnType) -> TokenStream {
        let body;
        let output_type;
        let ret_expr;
        match output {
            ReturnType::Default => {
                body = quote! {
                    #block
                    Ok(())
                };
                output_type =
                    quote!(::core::result::Result<_, ::proptest::test_runner::TestCaseError> );
                ret_expr = quote! { ret? };
            }
            ReturnType::Type(_, ty) => {
                body = quote! { #block };
                output_type = quote!(#ty);
                ret_expr = quote! {
                    ::std::result::Result::map_err(ret,
                        |e| ::proptest::test_runner::TestCaseError::fail(::std::string::ToString::to_string(&e)))?
                };
            }
        }
        match self {
            Async::Tokio => {
                quote! {
                    let ret: #output_type =
                        tokio::runtime::Runtime::new()
                            .unwrap()
                            .block_on(async move { #body });
                    #ret_expr;
                }
            }
            Async::Expr(expr) => {
                quote! {
                    let ret: #output_type =
                    (#expr)(async move { #body });
                    #ret_expr;
                }
            }
        }
    }
}
impl syn::parse::Parse for Async {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        if input.peek(LitStr) {
            let s: LitStr = input.parse()?;
            match s.value().as_str() {
                "tokio" => Ok(Async::Tokio),
                _ => bail!(s.span(), "expected `tokio`."),
            }
        } else {
            Ok(Async::Expr(input.parse()?))
        }
    }
}

struct TestFnAttrArgs {
    r#async: Option<Async>,
    dump: bool,
}
impl TestFnAttrArgs {
    fn from(args: Args) -> Result<(Self, Args)> {
        let mut config_args = Args::new();
        let mut this = TestFnAttrArgs {
            r#async: None,
            dump: false,
        };
        for arg in args {
            if let Arg::NameValue { name, value, .. } = &arg {
                if name == "async" {
                    this.r#async = Some(parse2(value.to_token_stream())?);
                    continue;
                }
            }
            if let Arg::Value(value) = &arg {
                if value == &parse_quote!(dump) {
                    this.dump = true;
                    continue;
                }
            }
            config_args.0.push(arg);
        }
        Ok((this, config_args))
    }
}

fn to_camel_case(s: &str) -> String {
    let mut upper = true;
    let mut r = String::new();
    for c in s.chars() {
        if c == '_' {
            upper = true;
        } else if upper {
            r.push_str(&c.to_uppercase().to_string());
            upper = false;
        } else {
            r.push(c);
        }
    }
    r
}
