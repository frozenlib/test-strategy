extern crate proc_macro;

#[macro_use]
mod syn_utils;
mod arbitrary;
mod proptest_fn;

use syn::{parse_macro_input, DeriveInput, ItemFn};
use syn_utils::into_macro_output;

#[proc_macro_attribute]
pub fn proptest(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let item_fn = parse_macro_input!(item as ItemFn);
    into_macro_output(proptest_fn::build_proptest(attr.into(), item_fn))
}

#[proc_macro_derive(
    Arbitrary,
    attributes(arbitrary, strategy, any, filter, weight, by_ref)
)]
pub fn derive_arbitrary(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    into_macro_output(arbitrary::derive_arbitrary(input))
}
