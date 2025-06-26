use anyhow::Result;
use quote::ToTokens;
use syn::{File, Item, ItemFn, Stmt, parse_quote, parse_str};

use crate::utils::rustfmt;

pub fn build() -> Result<()> {
    let s = std::fs::read_to_string("tests/arbitrary.rs")?;
    let mut file: File = parse_str(&s)?;
    transform(&mut file)?;
    let s = file.to_token_stream().to_string();
    let s = rustfmt(&s);
    std::fs::write("tests/arbitrary_in_macro_rules.rs", s)?;
    Ok(())
}

fn transform(file: &mut File) -> Result<()> {
    // 使用されているトレイトの組み合わせを収集
    let mut trait_combinations = std::collections::BTreeSet::new();
    collect_trait_combinations(file, &mut trait_combinations);

    // 必要なヘルパマクロを追加
    add_helper_macros(file, &trait_combinations);

    for item in &mut file.items {
        if let Item::Fn(fn_item) = item {
            if fn_item
                .attrs
                .iter()
                .any(|attr| attr.path().is_ident("test"))
            {
                transform_test_function(fn_item);
            }
        }
    }
    Ok(())
}

fn collect_trait_combinations(
    file: &File,
    combinations: &mut std::collections::BTreeSet<Vec<String>>,
) {
    for item in &file.items {
        if let Item::Fn(fn_item) = item {
            if fn_item
                .attrs
                .iter()
                .any(|attr| attr.path().is_ident("test"))
            {
                collect_from_function(fn_item, combinations);
            }
        }
    }
}

fn collect_from_function(
    fn_item: &ItemFn,
    combinations: &mut std::collections::BTreeSet<Vec<String>>,
) {
    for stmt in &fn_item.block.stmts {
        match stmt {
            Stmt::Item(item @ (Item::Struct(_) | Item::Enum(_))) => {
                if has_derive_arbitrary_attr(&item.attrs()) {
                    let traits = extract_derive_traits(&item.attrs());
                    combinations.insert(traits);
                }
            }
            _ => {}
        }
    }
}

fn extract_derive_traits(attrs: &[syn::Attribute]) -> Vec<String> {
    for attr in attrs {
        if attr.path().is_ident("derive") {
            if let syn::Meta::List(meta_list) = &attr.meta {
                let tokens_str = meta_list.tokens.to_string();
                return tokens_str
                    .split(',')
                    .map(|s| s.trim().to_string())
                    .collect();
            }
        }
    }
    vec![]
}

fn add_helper_macros(file: &mut File, combinations: &std::collections::BTreeSet<Vec<String>>) {
    let mut insert_index = 0;
    for (i, item) in file.items.iter().enumerate() {
        match item {
            Item::Use(_) => {
                insert_index = i + 1;
            }
            Item::Fn(_) => {
                break;
            }
            _ => {}
        }
    }

    for traits in combinations {
        if traits.contains(&"Arbitrary".to_string()) {
            let macro_name = generate_macro_name(traits);
            let helper_macro = create_helper_macro(&macro_name, traits);
            file.items.insert(insert_index, helper_macro);
            insert_index += 1;
        }
    }
}

fn generate_macro_name(traits: &[String]) -> String {
    let mut name = "macro_rules".to_string();
    for trait_name in traits {
        name.push('_');
        name.push_str(&trait_name.to_lowercase());
    }
    name
}

fn create_helper_macro(macro_name: &str, traits: &[String]) -> Item {
    let macro_ident = syn::Ident::new(macro_name, proc_macro2::Span::call_site());
    let trait_list = traits
        .iter()
        .map(|t| syn::Ident::new(t, proc_macro2::Span::call_site()))
        .collect::<Vec<_>>();

    parse_quote! {
        macro_rules! #macro_ident {
            ($item:item) => {
                #[derive(#(#trait_list),*)]
                $item
            };
        }
    }
}

fn transform_test_function(fn_item: &mut ItemFn) {
    let mut modified_stmts = Vec::new();
    let mut has_types = false;

    for stmt in &fn_item.block.stmts {
        match stmt {
            Stmt::Item(item @ (Item::Struct(_) | Item::Enum(_))) => {
                if has_derive_arbitrary_attr(&item.attrs()) {
                    has_types = true;

                    let traits = extract_derive_traits(&item.attrs());
                    let macro_name = generate_macro_name(&traits);

                    // derive属性を除去した型定義を作成
                    let mut cleaned_item = item.clone();
                    cleaned_item
                        .attrs_mut()
                        .retain(|attr| !attr.path().is_ident("derive"));

                    // 適切なヘルパマクロを使用してマクロ呼び出しを作成
                    let macro_ident = syn::Ident::new(&macro_name, proc_macro2::Span::call_site());
                    let macro_call: Stmt = parse_quote! {
                        #macro_ident! { #cleaned_item };
                    };
                    modified_stmts.push(macro_call);
                } else {
                    modified_stmts.push(stmt.clone());
                }
            }
            _ => {
                modified_stmts.push(stmt.clone());
            }
        }
    }

    if has_types {
        fn_item.block.stmts = modified_stmts;
    }
}

fn has_derive_arbitrary_attr(attrs: &[syn::Attribute]) -> bool {
    for attr in attrs {
        if attr.path().is_ident("derive") {
            if let syn::Meta::List(meta_list) = &attr.meta {
                let tokens_str = meta_list.tokens.to_string();
                if tokens_str.contains("Arbitrary") {
                    return true;
                }
            }
        }
    }
    false
}

trait ItemAttrs {
    fn attrs(&self) -> &[syn::Attribute];
    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute>;
}

impl ItemAttrs for Item {
    fn attrs(&self) -> &[syn::Attribute] {
        match self {
            Item::Struct(s) => &s.attrs,
            Item::Enum(e) => &e.attrs,
            _ => &[],
        }
    }

    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            Item::Struct(s) => &mut s.attrs,
            Item::Enum(e) => &mut e.attrs,
            _ => panic!("Unsupported item type"),
        }
    }
}
