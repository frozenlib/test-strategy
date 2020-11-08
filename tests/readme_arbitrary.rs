mod test_helpers;
use test_helpers::*;

#[test]
fn example_1() {
    use proptest::{
        arbitrary::any, arbitrary::Arbitrary, strategy::BoxedStrategy, strategy::Strategy,
    };
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    struct MyStructA {
        x: u32,
        y: u32,
    }
    #[derive(Debug, PartialEq)]
    struct MyStructB {
        x: u32,
        y: u32,
    }
    impl Arbitrary for MyStructB {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
            let x = any::<u32>();
            let y = any::<u32>();
            (x, y).prop_map(|(x, y)| Self { x, y }).boxed()
        }
    }

    assert_arbitrary(any::<MyStructB>().prop_map(|MyStructB { x, y }| MyStructA { x, y }));
}

#[test]
fn any_expr() {
    use proptest::collection::size_range;
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStructA {
        #[any(size_range(0..16).lift())]
        x: Vec<u16>,
    }

    use proptest::arbitrary::any_with;
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestStructB {
        #[strategy(any_with::<Vec<u16>>(size_range(0..16).lift()))]
        x: Vec<u16>,
    }

    use proptest::arbitrary::any;
    use proptest::strategy::Strategy;
    assert_eq_strategy(
        any::<TestStructA>(),
        any::<TestStructB>().prop_map(|TestStructB { x }| TestStructA { x }),
    );
}

#[test]
fn any_field() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestInputA {
        #[any(InnerArgs { upper : 20, ..InnerArgs::default() })]
        a: Inner,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestInputB {
        #[any(upper = 20)]
        a: Inner,
    }
    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestInputC {
        #[any(InnerArgs::default(), upper = 20)]
        a: Inner,
    }

    #[derive(Default)]
    struct InnerArgs {
        lower: i32,
        upper: i32,
    }

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(args = InnerArgs)]
    struct Inner {
        #[strategy(args.lower..args.upper)]
        x: i32,
    }

    use proptest::arbitrary::any;
    use proptest::strategy::Strategy;
    assert_eq_strategy(
        any::<TestInputA>(),
        any::<TestInputB>().prop_map(|TestInputB { a }| TestInputA { a }),
    );
    assert_eq_strategy(
        any::<TestInputA>(),
        any::<TestInputC>().prop_map(|TestInputC { a }| TestInputA { a }),
    );
}

#[test]
fn weight() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    enum TestInput {
        A,

        #[weight(2)]
        B,
    }
}

#[test]
fn weight_0() {
    use test_strategy::Arbitrary;

    #[derive(Debug)]
    struct NotArbitrary;

    #[derive(Arbitrary, Debug)]
    enum TestInput {
        A,

        #[allow(dead_code)]
        #[weight(0)]
        B(NotArbitrary),
    }
}

#[test]
fn filter_field_expr() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    struct TestInput {
        #[filter(#x % 2 == 0)]
        x: u32,
    }
}

#[test]
fn filter_struct_expr() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    #[filter((#x + #y) % 2 == 0)]
    struct TestInput {
        x: u32,
        y: u32,
    }
}

#[test]
fn filter_struct_expr_self() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    #[filter((#self.x + #self.y) % 2 == 0)]
    struct TestInput {
        x: u32,
        y: u32,
    }
}

#[test]
fn filter_field_fn() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    struct TestInput {
        #[filter(is_even)]
        x: u32,
    }
    fn is_even(x: &u32) -> bool {
        x % 2 == 0
    }
}

#[test]
fn filter_struct_fn() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    #[filter(x_is_even)]
    struct TestInput {
        x: u32,
    }
    fn x_is_even(input: &TestInput) -> bool {
        input.x % 2 == 0
    }
}

#[test]
fn filter_name() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    struct TestInput {
        #[filter("filter name", #x % 2 == 0)]
        x: u32,
    }
}

#[test]
fn by_ref_strategy() {
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug)]
    struct TestInput {
        #[by_ref]
        #[strategy(1..10u32)]
        x: u32,

        #[strategy(0..*#x)]
        y: u32,
    }
}

#[test]
fn arbitrary_args() {
    use test_strategy::Arbitrary;

    #[derive(Debug, Default)]
    struct TestInputArgs {
        x_max: u32,
    }

    #[derive(Arbitrary, Debug)]
    #[arbitrary(args = TestInputArgs)]
    struct TestInput {
        #[strategy(0..=args.x_max)]
        x: u32,
    }
}

#[test]
fn auto_bound() {
    use proptest::{
        arbitrary::any, arbitrary::Arbitrary, strategy::BoxedStrategy, strategy::Strategy,
    };
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    struct TestInputA<T> {
        x: T,
    }

    #[derive(Debug, PartialEq)]
    struct TestInputB<T> {
        x: T,
    }
    impl<T: Arbitrary + 'static> Arbitrary for TestInputB<T> {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
            any::<T>().prop_map(|x| Self { x }).boxed()
        }
    }

    assert_arbitrary(any::<TestInputB<u32>>().prop_map(|TestInputB { x }| TestInputA { x }));
}

#[test]
fn bound_both() {
    use proptest::arbitrary::any_with;
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T1, ..))]
    struct TestInput<T1, T2> {
        #[strategy(any_with::<T1>(Default::default()))]
        x: T1,

        y: T2,
    }
}

#[test]
fn manual_bound_type() {
    use proptest::arbitrary::any_with;
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T))]
    struct TestInput<T> {
        #[strategy(any_with::<T>(Default::default()))]
        x: T,
    }
}

#[test]
fn manual_bound_predicate() {
    use proptest::arbitrary::{any_with, Arbitrary};
    use test_strategy::Arbitrary;

    #[derive(Arbitrary, Debug, PartialEq)]
    #[arbitrary(bound(T : Arbitrary + 'static))]
    struct TestInput<T> {
        #[strategy(any_with::<T>(Default::default()))]
        x: T,
    }
}
