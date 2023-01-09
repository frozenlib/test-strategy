#![allow(clippy::derive_partial_eq_without_eq)]
mod test_helpers;

use proptest::{
    arbitrary::{any, any_with, Arbitrary},
    collection::size_range,
    prop_oneof,
    strategy::{Just, LazyJust, Strategy},
};
use std::fmt::Debug;
use test_helpers::*;
use test_strategy::Arbitrary;

#[test]
fn unit_struct() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct;
    assert_arbitrary(LazyJust::new(|| TestStruct));
}
#[test]
fn tuple_struct_no_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct();
    assert_arbitrary(LazyJust::new(TestStruct));
}
#[test]
fn struct_no_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {}
    assert_arbitrary(LazyJust::new(|| TestStruct {}));
}

#[test]
fn struct_no_attr_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        x: u16,
    }
    assert_arbitrary(any::<u16>().prop_map(|x| TestStruct { x }));
}

#[test]
fn struct_no_attr_field_x2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        x: u16,
        y: u8,
    }
    assert_arbitrary((any::<u16>(), any::<u8>()).prop_map(|(x, y)| TestStruct { x, y }));
}

#[test]
fn struct_field_raw_ident() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        r#x: u16,
    }
    assert_arbitrary(any::<u16>().prop_map(|x| TestStruct { x }));
}

#[test]
fn struct_field_raw_keyword_ident() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        r#fn: u16,
    }
    assert_arbitrary(any::<u16>().prop_map(|r#fn| TestStruct { r#fn }));
}

#[test]
fn tuple_struct_no_attr_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct(u16);
    assert_arbitrary(any::<u16>().prop_map(TestStruct));
}
#[test]
fn tuple_struct_no_attr_field_x2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct(u16, u8);
    assert_arbitrary((any::<u16>(), any::<u8>()).prop_map(|(x, y)| TestStruct(x, y)));
}

#[test]
fn strategy_struct() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..16u16)]
        x: u16,
    }
    assert_arbitrary((1..16u16).prop_map(|x| TestStruct { x }));
}

#[test]
fn strategy_struct_field_x2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..16u16)]
        x: u16,

        #[strategy(10..20u8)]
        y: u8,
    }
    assert_arbitrary((1..16u16, 10..20u8).prop_map(|(x, y)| TestStruct { x, y }));
}

#[test]
fn strategy_rank2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        x: u32,
        #[strategy(0..#x)]
        y: u32,
    }
    assert_arbitrary(
        (1..10u32)
            .prop_flat_map(|x| (0..x, Just(x)))
            .prop_map(|(y, x)| TestStruct { x, y }),
    );
}

#[test]
fn strategy_rank3() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        x: u32,
        #[strategy(0..#x)]
        y: u32,
        #[strategy(0..#y*2+1)]
        z: u32,
    }
    assert_arbitrary(
        (1..10u32)
            .prop_flat_map(|x| (0..x, Just(x)))
            .prop_flat_map(|(y, x)| (0..y * 2 + 1, Just(x), Just(y)))
            .prop_map(|(z, x, y)| TestStruct { x, y, z }),
    );
}

#[test]
fn strategy_underline() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..16u16)]
        _x: u16,
    }
}

#[test]
fn strategy_rev() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(0..#x)]
        y: u32,
        #[strategy(1..10u32)]
        x: u32,
    }
    assert_arbitrary(
        (1..10u32)
            .prop_flat_map(|x| (0..x, Just(x)))
            .prop_map(|(y, x)| TestStruct { x, y }),
    );
}

#[test]
fn strategy_tuple_struct() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct(#[strategy(1..10u32)] u32, #[strategy(0..#0)] u32);
    assert_arbitrary(
        (1..10u32)
            .prop_flat_map(|x| (0..x, Just(x)))
            .prop_map(|(y, x)| TestStruct(x, y)),
    );
}

#[test]
fn strategy_multiple_dependency() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(0..10)]
        x: i32,
        #[strategy(0..20)]
        y: i32,
        #[strategy(0..#x*#y+1)]
        z: i32,
    }
    assert_arbitrary(
        (0..10, 0..20)
            .prop_flat_map(|(x, y)| (0..x * y + 1, Just(x), Just(y)))
            .prop_map(|(z, x, y)| TestStruct { x, y, z }),
    );
}

#[test]
fn strategy_cross_dependency() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(0..10)]
        a: i32,
        #[strategy(0..20)]
        b: i32,
        #[strategy(0..30)]
        c: i32,
        #[strategy(0..#a * #b + 1)]
        x: i32,
        #[strategy(0..#b + #c + 10)]
        y: i32,
    }
    assert_arbitrary(
        (0..10, 0..20, 0..30)
            .prop_flat_map(|(a, b, c)| (0..a * b + 1, 0..b + c + 10, Just(a), Just(b), Just(c)))
            .prop_map(|(x, y, a, b, c)| TestStruct { a, b, c, x, y }),
    );
}

#[test]
fn strategy_by_ref() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[by_ref]
        #[strategy(1..10u32)]
        x: u32,
        #[strategy(0..*#x)]
        y: u32,
    }
    assert_arbitrary(
        (1..10u32)
            .prop_flat_map(|x| (0..x, Just(x)))
            .prop_map(|(y, x)| TestStruct { x, y }),
    );
}

#[test]
fn strategy_raw_keyword_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        r#fn: u32,
    }
    assert_arbitrary((1..10u32).prop_map(|r#fn| TestStruct { r#fn }));
}

#[test]
fn strategy_raw_keyword_sharp_val() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        r#fn: u32,
        #[strategy(0..#fn)]
        y: u32,
    }
    assert_arbitrary(
        (1..10u32)
            .prop_flat_map(|x| (0..x, Just(x)))
            .prop_map(|(y, r#fn)| TestStruct { r#fn, y }),
    );
}

#[test]
fn any_struct_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[any]
        x: u16,
    }
    assert_arbitrary(any::<u16>().prop_map(|x| TestStruct { x }));
}

#[test]
fn any_with_args_expr() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[any(size_range(0..16).lift())]
        x: Vec<u16>,
    }
    assert_arbitrary(any_with::<Vec<u16>>(size_range(0..16).lift()).prop_map(|x| TestStruct { x }));
}

mod sub_mod {

    #[allow(dead_code)]
    #[derive(Default)]
    pub struct TestArgsNoConstruct {
        a: u32,
    }
    impl TestArgsNoConstruct {
        pub fn new() -> Self {
            Self { a: 0 }
        }
    }
}

#[test]
fn any_with_args_expr_private_constructor() {
    #[derive(Arbitrary, Debug)]
    #[arbitrary(args = sub_mod::TestArgsNoConstruct)]
    struct Inner {
        #[allow(dead_code)]
        x: u32,
    }

    #[derive(Arbitrary, Debug)]
    struct TestInput {
        #[any(sub_mod::TestArgsNoConstruct::new())]
        #[allow(dead_code)]
        inner: Inner,
    }
}

#[test]
fn any_with_args_struct_field() {
    #[derive(Default)]
    struct TestArgs {
        a_max: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct Inner {
        #[strategy(0..args.a_max)]
        a: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    struct Outer {
        #[any(a_max = 50)]
        inner: Inner,
    }
    assert_arbitrary((0..50).prop_map(|a| Outer { inner: Inner { a } }));
}

#[test]
fn any_with_args_enum_field() {
    #[derive(Default)]
    struct TestArgs {
        a_max: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    enum Inner {
        A {
            #[strategy(0..args.a_max)]
            a: i32,
        },
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    struct Outer {
        #[any(a_max = 50)]
        inner: Inner,
    }
    assert_arbitrary((0..50).prop_map(|a| Outer {
        inner: Inner::A { a },
    }));
}

#[test]
fn any_with_args_field_x2() {
    #[derive(Default)]
    struct TestArgs {
        a_max1: i32,
        a_max2: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct Inner {
        #[strategy(0..args.a_max1 + args.a_max2)]
        a: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    struct Outer {
        #[any(a_max1 = 50, a_max2 = 10)]
        inner: Inner,
    }
    assert_arbitrary((0..60).prop_map(|a| Outer { inner: Inner { a } }));
}

#[test]
fn any_with_args_expr_field() {
    #[derive(Default)]
    struct TestArgs {
        a_max1: i32,
        a_max2: i32,
    }
    impl TestArgs {
        fn new() -> Self {
            Self {
                a_max1: 10,
                a_max2: 20,
            }
        }
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct Inner {
        #[strategy(0..args.a_max1 + args.a_max2)]
        a: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    struct Outer {
        #[any(TestArgs::new(), a_max2 = 30)]
        inner: Inner,
    }
    assert_arbitrary((0..40).prop_map(|a| Outer { inner: Inner { a } }));
}

#[test]
fn any_with_keyword() {
    #[derive(Default)]
    struct TestArgs {
        r#fn: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct Inner {
        #[strategy(0..args.r#fn)]
        a: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    struct Outer {
        #[any(fn = 50)]
        inner: Inner,
    }
    assert_arbitrary((0..50).prop_map(|a| Outer { inner: Inner { a } }));
}

#[test]
fn enum_unit_variant_1() {
    #[derive(Arbitrary, Debug, PartialEq)]
    enum TestEnum {
        X,
    }
    assert_arbitrary(LazyJust::new(|| TestEnum::X));
}

#[test]
fn enum_unit_variant_2() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    enum TestEnum {
        X,
        Y,
    }
    assert_arbitrary(prop_oneof![Just(TestEnum::X), Just(TestEnum::Y)]);
}

#[test]
fn enum_weight() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    enum TestEnum {
        #[weight(1)]
        X,
        #[weight(2)]
        Y,
    }
    assert_arbitrary(prop_oneof![1=>Just(TestEnum::X), 2=>Just(TestEnum::Y)]);
}

#[test]
fn enum_weight_0() {
    #[derive(Debug, PartialEq, Clone)]
    struct NotArbitrary;

    #[allow(dead_code)]
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    enum TestEnum {
        X,
        #[weight(0)]
        Y(NotArbitrary),
    }

    assert_arbitrary(Just(TestEnum::X));
}

#[test]
fn filter_struct_field_fn() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        #[filter(is_even)]
        x: u32,
    }
    fn is_even(value: &u32) -> bool {
        value % 2 == 0
    }
    assert_arbitrary(
        (1..10u32)
            .prop_filter("is_even", is_even)
            .prop_map(|x| TestStruct { x }),
    );
}

#[test]
fn filter_struct_field_fn_dependency() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        a: u32,
        #[filter(is_larger_than(#a))]
        b: u32,
    }

    fn is_larger_than(t: u32) -> impl Fn(&u32) -> bool {
        move |&value| value > t
    }
    assert_arbitrary(
        (any::<u32>(), any::<u32>())
            .prop_filter("is_larger_than(a)", |&(a, b)| is_larger_than(a)(&b))
            .prop_map(|(a, b)| TestStruct { a, b }),
    );
}

#[test]
fn filter_struct_field_sharp_val() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        #[filter(is_even(&#x))]
        x: u32,
    }
    fn is_even(value: &u32) -> bool {
        value % 2 == 0
    }
    assert_arbitrary(
        (1..10u32)
            .prop_filter("is_even", is_even)
            .prop_map(|x| TestStruct { x }),
    );
}

#[test]
fn filter_tuple_struct_field_sharp_val() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct(
        #[strategy(1..10u32)]
        #[filter(is_even(&#0))]
        u32,
    );
    fn is_even(value: &u32) -> bool {
        value % 2 == 0
    }
    assert_arbitrary(
        (1..10u32)
            .prop_filter("is_even", is_even)
            .prop_map(TestStruct),
    );
}

#[test]
fn filter_struct_field_closure() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        #[filter(|val| val % 2 == 0)]
        x: u32,
    }
    assert_arbitrary(
        (1..10u32)
            .prop_filter("is_even", |val| val % 2 == 0)
            .prop_map(|x| TestStruct { x }),
    );
}

#[test]
fn filter_struct_sharp_vals() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[filter(#x > #y)]
    struct TestStruct {
        x: u32,
        y: u32,
    }
    assert_arbitrary(
        (any::<u32>(), any::<u32>())
            .prop_filter("x > y", |&(x, y)| x > y)
            .prop_map(|(x, y)| TestStruct { x, y }),
    );
}

#[test]
fn filter_struct_sharp_self() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[filter(#self.x > #self.y)]
    struct TestStruct {
        x: u32,
        y: u32,
    }
    assert_arbitrary(
        (any::<u32>(), any::<u32>())
            .prop_filter("x > y", |&(x, y)| x > y)
            .prop_map(|(x, y)| TestStruct { x, y }),
    );
}

#[test]
fn filter_struct_fn() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[filter(|s| s.x > s.y)]
    struct TestStruct {
        x: u32,
        y: u32,
    }
    assert_arbitrary(
        (any::<u32>(), any::<u32>())
            .prop_filter("x > y", |&(x, y)| x > y)
            .prop_map(|(x, y)| TestStruct { x, y }),
    );
}

#[test]
fn filter_enum_fn() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    #[filter(Self::is_valid)]
    enum TestEnum {
        A(i32),
        B(i32),
    }
    impl TestEnum {
        fn is_valid(&self) -> bool {
            match self {
                Self::A(x) => x % 2 == 0,
                Self::B(x) => x % 2 != 0,
            }
        }
    }

    assert_arbitrary(
        prop_oneof![
            any::<i32>().prop_map(TestEnum::A),
            any::<i32>().prop_map(TestEnum::B),
        ]
        .prop_filter("is_valid", TestEnum::is_valid),
    );
}

#[test]
fn filter_enum_sharp_self() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    #[filter(#self.is_valid())]
    enum TestEnum {
        A(i32),
        B(i32),
    }
    impl TestEnum {
        fn is_valid(&self) -> bool {
            match self {
                Self::A(x) => x % 2 == 0,
                Self::B(x) => x % 2 != 0,
            }
        }
    }
    assert_arbitrary(
        prop_oneof![
            any::<i32>().prop_map(TestEnum::A),
            any::<i32>().prop_map(TestEnum::B),
        ]
        .prop_filter("is_valid", TestEnum::is_valid),
    );
}

#[test]
fn filter_variant() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    enum TestEnum {
        #[filter(#x > #y)]
        A {
            x: i32,
            y: i32,
        },
        B(i32),
    }
    assert_arbitrary(prop_oneof![
        (any::<i32>(), any::<i32>())
            .prop_filter("x > y", |&(x, y)| x > y)
            .prop_map(|(x, y)| TestEnum::A { x, y }),
        any::<i32>().prop_map(TestEnum::B),
    ]);
}

#[test]
fn filter_raw_keyword() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[filter(#fn > #y)]
    struct TestStruct {
        r#fn: u32,
        y: u32,
    }
    assert_arbitrary(
        (any::<u32>(), any::<u32>())
            .prop_filter("fn > y", |&(r#fn, y)| r#fn > y)
            .prop_map(|(r#fn, y)| TestStruct { r#fn, y }),
    );
}

#[test]
fn filter_with_whence() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct {
        #[strategy(1..10u32)]
        #[filter("is_even", is_even)]
        x: u32,
    }
    fn is_even(value: &u32) -> bool {
        value % 2 == 0
    }
    assert_arbitrary(
        (1..10u32)
            .prop_filter("is_even", is_even)
            .prop_map(|x| TestStruct { x }),
    );
}

#[test]
fn filter_with_by_ref() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[filter(#x > *#y)]
    struct TestStruct {
        x: u32,
        #[by_ref]
        y: u32,
    }
    assert_arbitrary(
        (any::<u32>(), any::<u32>())
            .prop_filter("x > y", |&(x, y)| x > y)
            .prop_map(|(x, y)| TestStruct { x, y }),
    );
}

#[test]
fn args_struct() {
    #[derive(Default)]
    struct TestArgs {
        x_max: u32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[strategy(0..args.x_max)]
        x: u32,
    }
}

#[test]
fn args_with_strategy_sharp_val() {
    #[derive(Default)]
    struct TestArgs {
        y: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[strategy(0..10)]
        x: i32,

        #[strategy(0..#x + args.y)]
        y: i32,
    }
}
#[test]
fn args_with_strategy_sharp_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        a: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[strategy(0..10)]
        x: i32,

        #[strategy(0..#x + args.a)]
        y: i32,

        #[strategy(0..#y + args.a)]
        z: i32,
    }
}

#[test]
fn args_with_struct_filter_sharp_val() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(#x % args.m != 0)]
    struct TestStruct {
        x: i32,
    }
}

#[test]
fn args_with_struct_filter_sharp_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(#x % args.m != 0)]
    #[filter(#x % args.m != 1)]
    struct TestStruct {
        x: i32,
    }
}

#[test]
fn args_with_struct_filter_sharp_self() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(#self.x % args.m != 0)]
    struct TestStruct {
        x: i32,
    }
}

#[test]
fn args_with_struct_filter_sharp_self_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(#self.x % args.m != 0)]
    #[filter(#self.x % args.m != 1)]
    struct TestStruct {
        x: i32,
    }
}

#[test]
fn args_with_struct_filter_fn() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(is_valid_fn(args.m))]
    struct TestStruct {
        x: i32,
    }

    fn is_valid_fn(_: i32) -> impl Fn(&TestStruct) -> bool {
        |_| true
    }
}

#[test]
fn args_with_struct_filter_fn_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(is_valid_fn(args.m))]
    #[filter(is_valid_fn(args.m + 1))]
    struct TestStruct {
        x: i32,
    }

    fn is_valid_fn(_: i32) -> impl Fn(&TestStruct) -> bool {
        |_| true
    }
}

#[test]
fn args_with_enum_filter_sharp_val() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(#self.is_valid(args.m))]
    enum TestEnum {
        A { x: i32 },
        B,
    }

    impl TestEnum {
        fn is_valid(&self, m: i32) -> bool {
            match self {
                Self::A { x } => x % m != 0,
                Self::B => true,
            }
        }
    }
}

#[test]
fn args_with_enum_filter_sharp_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    #[filter(#self.is_valid(args.m))]
    #[filter(#self.is_valid(args.m + 1))]
    enum TestEnum {
        A { x: i32 },
        B,
    }

    impl TestEnum {
        fn is_valid(&self, m: i32) -> bool {
            match self {
                Self::A { x } => x % m != 0,
                Self::B => true,
            }
        }
    }
}

#[test]
fn args_with_variant_filter_sharp_val() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    enum TestEnum {
        #[filter(#x % args.m != 0)]
        A {
            x: i32,
        },
        B,
    }
}

#[test]
fn args_with_variant_filter_sharp_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    enum TestEnum {
        #[filter(#x % args.m != 0)]
        #[filter(#x % args.m != 1)]
        A {
            x: i32,
        },
        B,
    }
}

#[test]
fn args_with_field_filter_sharp_val() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[filter(#x % args.m != 0)]
        x: i32,
    }
}

#[test]
fn args_with_field_filter_sharp_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[filter(#x % args.m != 0)]
        #[filter(#x % args.m != 1)]
        x: i32,
    }
}

#[test]
fn args_with_field_filter_fn() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[filter(is_larger_than(args.m))]
        x: i32,
    }

    fn is_larger_than(t: i32) -> impl Fn(&i32) -> bool {
        move |x: &i32| *x > t
    }
}

#[test]
fn args_with_field_filter_fn_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[filter(is_larger_than(args.m))]
        #[filter(is_larger_than(args.m + 1))]
        x: i32,
    }

    fn is_larger_than(t: i32) -> impl Fn(&i32) -> bool {
        move |x: &i32| *x > t
    }
}

#[test]
fn args_map() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[map(|x: i32| x + args.m)]
        x: i32,
    }
}
#[test]
fn args_map_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[map(|x: i32| x + args.m)]
        x: i32,

        #[map(|y: i32| y + args.m)]
        y: i32,
    }
}

#[test]
fn args_map_filter_val() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[map(|x: i32| x + args.m)]
        #[filter(#x > args.m)]
        x: i32,
    }
}

#[test]
fn args_map_filter_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[map(|x: i32| x + args.m)]
        #[filter(#x > args.m)]
        #[filter(#x > args.m + 1)]
        x: i32,
    }
}

#[test]
fn args_map_filter_fn_val() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[map(|x: i32| x + args.m)]
        #[filter(|&x: &i32| x > args.m)]
        x: i32,
    }
}

#[test]
fn args_map_filter_fn_val_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        #[map(|x: i32| x + args.m)]
        #[filter(|&x: &i32| x > args.m)]
        #[filter(|&x: &i32| x > args.m + 1)]
        x: i32,
    }
}

#[test]
fn args_flat_map_x2() {
    #[derive(Default)]
    struct TestArgs {
        m: i32,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = TestArgs)]
    struct TestStruct {
        a0: i32,
        a1: i32,
        #[strategy(#a0..#a1 + args.m)]
        b0: i32,
        #[strategy(#a0..#a1 + args.m)]
        b1: i32,
    }
}

#[test]
fn auto_bound_tuple_struct() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct<T>(T);

    assert_arbitrary(any::<u16>().prop_map(TestStruct));
    assert_arbitrary(any::<u32>().prop_map(TestStruct));
}

#[test]
fn auto_bound_tuple_enum() {
    #[derive(Arbitrary, Debug, PartialEq)]
    enum TestEnum<T> {
        A(T),
    }

    assert_arbitrary(any::<u16>().prop_map(TestEnum::A));
    assert_arbitrary(any::<u32>().prop_map(TestEnum::A));
}

#[test]
fn auto_bound_any_attribute() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct<T>(#[any(std::default::Default::default())] T);

    assert_arbitrary(any::<u16>().prop_map(TestStruct));
    assert_arbitrary(any::<u32>().prop_map(TestStruct));
}

#[test]
fn auto_bound_x2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStruct<T1, T2>(T1, T2);

    assert_arbitrary((any::<u16>(), any::<u32>()).prop_map(|(x, y)| TestStruct(x, y)));
}

#[test]
fn auto_bound_map_input() {
    #[derive(Debug, PartialEq, Clone)]
    struct Wrapped<T>(T);

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T: Clone, ..))]
    struct TestStruct<T> {
        #[by_ref]
        #[map(|t: T| Wrapped(t))]
        t: Wrapped<T>,
    }
}

#[test]
fn manual_bound_type() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T))]
    struct TestStruct<T> {
        #[strategy(any::<T>())]
        x: T,
    }

    assert_arbitrary(any::<u16>().prop_map(|x| TestStruct { x }));
    assert_arbitrary(any::<u32>().prop_map(|x| TestStruct { x }));
}
#[test]
fn manual_bound_type_x2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T1, T2))]
    struct TestStruct<T1, T2> {
        #[strategy(any::<T1>())]
        x: T1,

        #[strategy(any::<T2>())]
        y: T2,
    }

    assert_arbitrary((any::<u16>(), any::<u32>()).prop_map(|(x, y)| TestStruct { x, y }));
}

#[test]
fn manual_bound_type_with_auto_bound() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T1, ..))]
    struct TestStruct<T1, T2> {
        #[strategy(any::<T1>())]
        x: T1,
        y: T2,
    }

    assert_arbitrary((any::<u16>(), any::<u32>()).prop_map(|(x, y)| TestStruct { x, y }));
}

#[test]
fn manual_bound_predicate() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T : Arbitrary + 'static))]
    struct TestStruct<T> {
        #[strategy(any::<T>())]
        x: T,
    }

    assert_arbitrary(any::<u16>().prop_map(|x| TestStruct { x }));
    assert_arbitrary(any::<u32>().prop_map(|x| TestStruct { x }));
}

#[test]
fn manual_bound_predicate_x2() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T1 : Arbitrary + 'static, T2 : Arbitrary + 'static))]
    struct TestStruct<T1, T2> {
        #[strategy(any::<T1>())]
        x: T1,

        #[strategy(any::<T2>())]
        y: T2,
    }

    assert_arbitrary((any::<u16>(), any::<u32>()).prop_map(|(x, y)| TestStruct { x, y }));
}

#[test]
fn manual_bound_field() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T : Copy + Arbitrary + 'static))]
    struct Inner<T>(T);

    #[derive(Arbitrary, Debug, PartialEq)]
    pub struct Outer<T> {
        #[arbitrary(bound(T : Debug + Copy + Arbitrary + 'static))]
        x: Inner<T>,
    }
    assert_arbitrary(any::<u16>().prop_map(|x| Outer { x: Inner(x) }));
}

#[test]
fn manual_bound_variant() {
    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T : Copy + Arbitrary + 'static))]
    pub struct Inner<T>(T);

    #[derive(Arbitrary, Debug, PartialEq)]
    pub enum Outer<T> {
        #[arbitrary(bound(T : Debug + Copy + Arbitrary + 'static))]
        X(Inner<T>),
    }
    assert_arbitrary(any::<u16>().prop_map(|x| Outer::X(Inner(x))));
}

#[test]
fn enum_with_variant_named_parameters() {
    #[deny(warnings)]
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    enum MyEnum {
        Parameters,
        SomethingElse,
    }
}

#[test]
fn map() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[map(|x: u32| x + 1)]
        x: u32,
    }

    assert_arbitrary(any::<u32>().prop_map(|x| X { x: x + 1 }));
}

#[test]
fn map_dependency() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        a: u32,
        #[map(|x: u32| x ^ #a)]
        b: u32,
    }

    assert_arbitrary((any::<u32>(), any::<u32>()).prop_map(|x| X {
        a: x.0,
        b: x.0 ^ x.1,
    }));
}

#[test]
fn map_dependency_by_ref() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[by_ref]
        a: u32,
        #[map(|x: u32| x ^ *#a)]
        b: u32,
    }

    assert_arbitrary((any::<u32>(), any::<u32>()).prop_map(|x| X {
        a: x.0,
        b: x.0 ^ x.1,
    }));
}

#[test]
fn map_filter() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[map(|x: u32| x + 1)]
        #[filter(#x % 2 == 0)]
        x: u32,
    }

    assert_arbitrary(
        any::<u32>()
            .prop_map(|x| x + 1)
            .prop_filter("", |x| x % 2 == 0)
            .prop_map(|x| X { x }),
    );
}

#[test]
fn map_strategy() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[strategy(1..10u32)]
        #[map(|x: u32| x * 2)]
        x: u32,
    }

    assert_arbitrary((1..10u32).prop_map(|x| X { x: x * 2 }));
}

#[test]
fn map_strategy_infer() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[strategy(1..10u32)]
        #[map(|x| x * 2)]
        x: u32,
    }

    assert_arbitrary((1..10u32).prop_map(|x| X { x: x * 2 }));
}

#[test]
fn map_strategy_any() {
    fn x2(x: u32) -> u32 {
        x * 2
    }
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[map(x2)]
        x: u32,
    }
    assert_arbitrary((any::<u32>()).prop_map(|x| X { x: x * 2 }));
}

#[test]
fn map_strategy_any_with() {
    fn x2(x: A) -> u32 {
        x.0 * 2
    }

    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    #[arbitrary(args = u32)]
    struct A(#[strategy(0..*args)] u32);

    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[any(10)]
        #[map(x2)]
        x: u32,
    }
    assert_arbitrary((0..10u32).prop_map(|x| X { x: x * 2 }));
}

#[test]
fn map_strategy_any_with_setter() {
    fn x2(x: A) -> u32 {
        x.0 * 2
    }

    #[derive(Default)]
    struct Arg {
        val: u32,
    }

    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    #[arbitrary(args = Arg)]
    struct A(#[strategy(0..args.val)] u32);

    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[any(val = 10)]
        #[map(x2)]
        x: u32,
    }
    assert_arbitrary((0..10u32).prop_map(|x| X { x: x * 2 }));
}

#[test]
fn map_strategy_any_dependency() {
    fn xor(arg: u32) -> impl Fn(u32) -> u32 {
        move |x| x ^ arg
    }
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        a: u32,
        #[map(xor(#a))]
        b: u32,
    }
    assert_arbitrary((any::<u32>(), any::<u32>()).prop_map(|x| X {
        a: x.0,
        b: x.0 ^ x.1,
    }));
}

#[test]
fn map_strategy_any_dependency_by_ref() {
    fn xor(arg: u32) -> impl Fn(u32) -> u32 {
        move |x| x ^ arg
    }
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[by_ref]
        a: u32,
        #[map(xor(*#a))]
        b: u32,
    }
    assert_arbitrary((any::<u32>(), any::<u32>()).prop_map(|x| X {
        a: x.0,
        b: x.0 ^ x.1,
    }));
}

#[test]
fn depend_on_map() {
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[strategy(0..5u32)]
        #[map(|x: u32| x + 5)]
        a: u32,

        #[strategy(0..#a)]
        b: u32,
    }

    assert_arbitrary(
        (0..5u32)
            .prop_flat_map(|x| (Just(x + 5), 0..x + 5))
            .prop_map(|x| X { a: x.0, b: x.1 }),
    );
}

#[test]
fn index() {
    use proptest::sample::Index;
    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[strategy(1..20usize)]
        a: usize,
        #[map(|i: Index| i.index(#a))]
        b: usize,
    }

    assert_arbitrary((1..20usize, any::<Index>()).prop_map(|x| X {
        a: x.0,
        b: x.1.index(x.0),
    }));
}

#[test]
fn filter_with_strategy_and_map() {
    use proptest::sample::Index;

    #[derive(Arbitrary, Debug, PartialEq, Clone)]
    struct X {
        #[strategy(10..100usize)]
        a: usize,

        #[strategy(0..#a)]
        x: usize,

        #[map(|i: Index|i.index(#a))]
        #[filter(#y % 2 == 0)]
        y: usize,
    }

    let s = (10..100usize, any::<Index>())
        .prop_flat_map(|x| {
            (
                0..x.0,
                Just(x.1.index(x.0)).prop_filter("", |y| y % 2 == 0),
                Just(x.0),
                Just(x.1),
            )
        })
        .prop_map(|x| X {
            a: x.2,
            x: x.0,
            y: x.1,
        });

    assert_arbitrary(s);
}
