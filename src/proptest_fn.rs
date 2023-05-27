use crate::syn_utils::{Arg, Args};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse2, parse_quote, parse_str, spanned::Spanned, token, Block, Field, FieldMutability, FnArg,
    Ident, ItemFn, LitStr, Pat, Result, Visibility,
};

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
    let block = if let Some(a) = attr_args.r#async {
        item_fn.sig.asyncness = None;
        a.apply(block)
    } else {
        quote!(#block)
    };
    let block = quote! {
        {
            let #args_type_ident { #(#args_pats,)* } = input;
            #block
        }
    };
    item_fn.sig.inputs = parse_quote! { input: #args_type_ident };
    item_fn.block = Box::new(parse2(block)?);
    let args_fields = args.iter().map(|arg| &arg.field);
    let config = to_proptest_config(config_args);
    let ts = quote! {
        #[derive(test_strategy::Arbitrary, Debug)]
        struct #args_type_ident {
            #(#args_fields,)*
        }
        proptest::proptest! {
            #config
            #[test]
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

#[derive(Debug, Clone, Copy)]
enum Async {
    Tokio,
}
impl Async {
    fn apply(&self, block: &Block) -> TokenStream {
        match self {
            Async::Tokio => {
                quote! {
                    let ret: ::core::result::Result<_, proptest::test_runner::TestCaseError> =
                        tokio::runtime::Runtime::new()
                            .unwrap()
                            .block_on(async move {
                                #block
                                Ok(())
                            });
                    ret?;
                }
            }
        }
    }
}
impl syn::parse::Parse for Async {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let s: LitStr = input.parse()?;
        match s.value().as_str() {
            "tokio" => Ok(Async::Tokio),
            _ => bail!(s.span(), "expected `tokio`."),
        }
    }
}

struct TestFnAttrArgs {
    r#async: Option<Async>,
}
impl TestFnAttrArgs {
    fn from(args: Args) -> Result<(Self, Args)> {
        let mut config_args = Args::new();
        let mut this = TestFnAttrArgs { r#async: None };
        for arg in args {
            if let Arg::NameValue { name, value, .. } = &arg {
                if name == "async" {
                    this.r#async = Some(parse2(value.to_token_stream())?);
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
