use proc_macro2::TokenStream;
use std::ops::{Deref, DerefMut};
use syn::Token;
use syn::{
    parse::{discouraged::Speculative, Parse, ParseStream},
    parse_quote, Result, Type, WherePredicate,
};

#[allow(clippy::large_enum_variant)]
pub enum Bound {
    Type(Type),
    Predicate(WherePredicate),
    Default(Token![..]),
}
impl Parse for Bound {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![..]) {
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

pub struct Bounds {
    pub ty: Vec<Type>,
    pub pred: Vec<WherePredicate>,
    pub can_extend: bool,
}
impl Bounds {
    pub fn new(can_extend: bool) -> Self {
        Bounds {
            ty: Vec::new(),
            pred: Vec::new(),
            can_extend,
        }
    }
    pub fn from_data(bound: Option<Vec<Bound>>) -> Self {
        if let Some(bound) = bound {
            let mut bs = Self::new(false);
            for b in bound {
                bs.push(b);
            }
            bs
        } else {
            Self::new(true)
        }
    }
    fn push(&mut self, bound: Bound) {
        match bound {
            Bound::Type(ty) => self.ty.push(ty),
            Bound::Predicate(pred) => self.pred.push(pred),
            Bound::Default(_) => self.can_extend = true,
        }
    }
    pub fn child(&mut self, bound: Option<Vec<Bound>>) -> BoundsChild {
        let bounds = if self.can_extend {
            Self::from_data(bound)
        } else {
            Self::new(false)
        };
        BoundsChild {
            owner: self,
            bounds,
        }
    }
    pub fn build_wheres(self, type_param_bounds: TokenStream) -> Vec<WherePredicate> {
        let mut pred = self.pred;
        for ty in self.ty {
            pred.push(parse_quote!(#ty : #type_param_bounds));
        }
        pred
    }
}
pub struct BoundsChild<'a> {
    owner: &'a mut Bounds,
    bounds: Bounds,
}
impl<'a> Deref for BoundsChild<'a> {
    type Target = Bounds;

    fn deref(&self) -> &Self::Target {
        &self.bounds
    }
}
impl<'a> DerefMut for BoundsChild<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bounds
    }
}
impl<'a> Drop for BoundsChild<'a> {
    fn drop(&mut self) {
        if self.owner.can_extend {
            self.owner.ty.extend(self.bounds.ty.drain(..));
            self.owner.pred.extend(self.bounds.pred.drain(..));
        }
    }
}
