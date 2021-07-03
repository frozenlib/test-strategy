use crate::syn_utils::{Arg, Args};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse2, parse_quote, parse_str, spanned::Spanned, token, Field, FnArg, Ident, ItemFn, Pat,
    Result, Visibility,
};

pub fn build_proptest(attr: TokenStream, mut item_fn: ItemFn) -> Result<TokenStream> {
    let mut attr_args = None;
    if !attr.is_empty() {
        attr_args = Some(parse2::<Args>(attr)?);
    }
    let mut dump = false;
    item_fn.attrs.retain(|attr| {
        if attr.path.is_ident("proptest_dump") {
            dump = true;
            false
        } else {
            true
        }
    });
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
    let block = quote! {
        {
            let #args_type_ident { #(#args_pats,)* } = input;
            #block
        }
    };
    item_fn.sig.inputs = parse_quote! { input: #args_type_ident };
    item_fn.block = Box::new(parse2(block)?);
    let args_fields = args.iter().map(|arg| &arg.field);
    let config = to_proptest_config(attr_args);
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

fn to_proptest_config(args: Option<Args>) -> TokenStream {
    if let Some(args) = args {
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
    } else {
        quote! {}
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
                            ident: Some(ident.ident.clone()),
                            colon_token: Some(arg.colon_token),
                            ty: arg.ty.as_ref().clone(),
                        },
                        mutability: ident.mutability.clone(),
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
