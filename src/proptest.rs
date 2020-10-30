use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse2, parse_macro_input, parse_quote, parse_str, spanned::Spanned, DeriveInput, Field, FnArg,
    Ident, ItemFn, Pat, Result, Visibility,
};
use syn_utils::into_macro_output;

pub fn build_proptest(mut item_fn: ItemFn) -> Result<TokenStream> {
    item_fn.attrs.push(parse_quote!(#[test]));
    let args_type_str = to_camel_case(&item_fn.sig.ident.to_string()) + "Args";
    let args_type_ident: Ident = parse_str(&args_type_str).unwrap();
    let args_fields = item_fn
        .sig
        .inputs
        .iter()
        .map(to_field)
        .collect::<Result<Vec<_>>>()?;
    let args_field_names = args_fields
        .iter()
        .map(|field| field.ident.as_ref().unwrap());
    let block = &item_fn.block;
    let block = quote! {
        {
            let #args_type_ident { #(#args_field_names,)* } = input;
            #block
        }
    };
    item_fn.sig.inputs = parse_quote! { input: #args_type_ident };
    item_fn.block = Box::new(parse2(block)?);
    Ok(quote! {
        #[derive(test_strategy::Arbitrary, Debug)]
        struct #args_type_ident {
            #(#args_fields,)*
        }
        proptest::proptest! {
            #[test]
            #item_fn
        }
    })
}

fn to_field(arg: &FnArg) -> Result<Field> {
    if let FnArg::Typed(arg) = arg {
        if let Pat::Ident(ident) = arg.pat.as_ref() {
            if ident.attrs.is_empty() && ident.by_ref.is_none() && ident.subpat.is_none() {
                return Ok(Field {
                    attrs: arg.attrs.clone(),
                    vis: Visibility::Inherited,
                    ident: Some(ident.ident.clone()),
                    colon_token: Some(arg.colon_token),
                    ty: arg.ty.as_ref().clone(),
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
