// #![include_doc("../README.md", start("This crate provides two procedural macros, `#[derive(Arbitrary)]` and `#[proptest]`."))]
//! This crate provides two procedural macros, `#[derive(Arbitrary)]` and `#[proptest]`.
//!
//! Each of these macros is an alternative to the following proptest's official macros.
//!
//! | [test-strategy][]                          | [proptest][]                  | [proptest-derive][]                 |
//! | ------------------------------------------ | ----------------------------- | ----------------------------------- |
//! | [`#[derive(Arbitrary)]`](#derivearbitrary) |                               | [`#[derive(Arbitrary)]`][offical-a] |
//! | [`#[proptest]`](#proptest)                 | [`proptest ! { }`][offical-m] |                                     |
//!
//! [test-strategy]: https://crates.io/crates/test-strategy
//! [proptest]: https://crates.io/crates/proptest
//! [proptest-derive]: https://crates.io/crates/proptest-derive
//! [offical-m]: https://altsysrq.github.io/rustdoc/proptest/latest/proptest/macro.proptest.html
//! [offical-a]: https://altsysrq.github.io/proptest-book/proptest-derive/modifiers.html
//!
//! The macros provided by this crate have the following advantages over the proptest's official macros.
//!
//! - Supports higher-order strategies. (`#[derive(Arbitrary)]` and `#[proptest]`)
//! - Code formatting is not disabled. (`#[proptest]`)
//!
//! However, the syntax of this crate's macros are not compatible with the syntax of the official macros.
//!
//! ## Install
//!
//! Add this to your Cargo.toml:
//!
//! ```toml
//! [dependencies]
//! test-strategy = "0.3.1"
//! proptest = "1.0.0"
//! ```
//!
//! ## Example
//!
//! You can use `#[derive(Arbitrary)]` to automatically implement proptest's `Arbitrary` trait.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInputStruct {
//!     x: u32,
//!
//!     #[strategy(1..10u32)]
//!     y: u32,
//!
//!     #[strategy(0..#y)]
//!     z: u32,
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! enum TestInputEnum {
//!     A,
//!     B,
//!     #[weight(3)]
//!     C,
//!     X(u32),
//!     Y(#[strategy(0..10u32)] u32),
//! }
//! ```
//!
//! You can define a property test by adding `#[proptest]` to the function.
//!
//! ```rust
//! use test_strategy::proptest;
//!
//! #[proptest]
//! fn my_test(_x: u32, #[strategy(1..10u32)] y: u32, #[strategy(0..#y)] z: u32) {
//!     assert!(1 <= y && y < 10);
//!     assert!(z <= y);
//! }
//! ```
//!
//! ## Attributes
//!
//! Attributes can be written in the following positions.
//!
//! | attribute                                           | function | struct | enum | variant | field | function parameter |
//! | --------------------------------------------------- | -------- | ------ | ---- | ------- | ----- | ------------------ |
//! | [`#[strategy]`](#strategy)                          |          |        |      |         | ✔     | ✔                  |
//! | [`#[any]`](#any)                                    |          |        |      |         | ✔     | ✔                  |
//! | [`#[weight]`](#weight)                              |          |        |      | ✔       |       |                    |
//! | [`#[map]`](#map)                                    |          |        |      |         | ✔     | ✔                  |
//! | [`#[filter]`](#filter)                              | ✔        | ✔      | ✔    | ✔       | ✔     | ✔                  |
//! | [`#[by_ref]`](#by_ref)                              |          |        |      |         | ✔     | ✔                  |
//! | [`#[arbitrary(args = T)]`](#arbitraryargs--t)       |          | ✔      | ✔    |         |       |                    |
//! | [`#[arbitrary(bound(...))]`](#arbitraryboundt1-t2-) |          | ✔      | ✔    | ✔       | ✔     |                    |
//! | [`#[arbitrary(dump)]`](#arbitrarydump)              |          | ✔      | ✔    |         |       |                    |
//! | [`#[proptest]`](#proptest)                          | ✔        |        |      |         |       |                    |
//! | [`#[proptest(async = ...)]`](#proptestasync--)      | ✔        |        |      |         |       |                    |
//! | [`#[proptest(dump)]`](#proptestdump)                | ✔        |        |      |         |       |                    |
//!
//! ## `#[derive(Arbitrary)]`
//!
//! You can implement `proptest::arbitrary::Arbitrary` automatically by adding `#[derive(Arbitrary)]` to struct or enum declaration.
//!
//! By default, all fields are set using the strategy obtained by `proptest::arbitrary::any()`.
//!
//! So the following two codes are equivalent.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     x: u32,
//!     y: u32,
//! }
//! ```
//!
//! ```rust
//! use proptest::{
//!     arbitrary::{any, Arbitrary},
//!     strategy::{BoxedStrategy, Strategy},
//! };
//!
//! #[derive(Debug)]
//! struct TestInput {
//!     x: u32,
//!     y: u32,
//! }
//! impl Arbitrary for TestInput {
//!     type Parameters = ();
//!     type Strategy = BoxedStrategy<Self>;
//!
//!     fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
//!         let x = any::<u32>();
//!         let y = any::<u32>();
//!         (x, y).prop_map(|(x, y)| Self { x, y }).boxed()
//!     }
//! }
//! ```
//!
//! ## `#[strategy]`
//!
//! You can specify a strategy to generate values for the field by adding `#[strategy(...)]` to the field.
//!
//! In the following example, the value of field `x` will be less than 20.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     #[strategy(0..20u32)]
//!     x: u32,
//! }
//! ```
//!
//! In `#[strategy]`, the values of other fields can be used by following `#` to the name of the field.
//!
//! In the following example, the value of `y` is less than or equal to `x`.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     x: u32,
//!     #[strategy(0..=#x)]
//!     y: u32,
//! }
//! ```
//!
//! ## `#[any]`
//!
//! Instead of writing `#[strategy(any_with::<Type>(expr))]`, you can write `#[any(expr)]`.
//!
//! ```rust
//! use proptest::collection::size_range;
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug, PartialEq)]
//! struct TestInput {
//!     #[any(size_range(0..16).lift())]
//!     x: Vec<u16>,
//! }
//! ```
//!
//! Instead of writing an expression to be passed to `any_with`, you can write only the value of the field to be changed from the default value.
//!
//! Therefore, the following `TestInputA`, `TestInputB` and `TestInputC` are equivalent.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInputA {
//!     #[any(InnerArgs { upper : 20, ..InnerArgs::default() })]
//!     a: Inner,
//! }
//! #[derive(Arbitrary, Debug)]
//! struct TestInputB {
//!     #[any(InnerArgs::default(), upper = 20)]
//!     a: Inner,
//! }
//! #[derive(Arbitrary, Debug)]
//! struct TestInputC {
//!     #[any(upper = 20)]
//!     a: Inner,
//! }
//!
//! #[derive(Default)]
//! struct InnerArgs {
//!     lower: i32,
//!     upper: i32,
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! #[arbitrary(args = InnerArgs)]
//! struct Inner {
//!     #[strategy(args.lower..args.upper)]
//!     x: i32,
//! }
//! ```
//!
//! ## `#[weight]`
//!
//! By default, all variants appear with equal probability.
//!
//! You can add `#[weight]` to the variant to change the probability of the variant appearing.
//!
//! In the following example, `TestInput::B` is twice as likely to appear as `TestInput::A`.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! enum TestInput {
//!     A,
//!
//!     #[weight(2)]
//!     B,
//! }
//! ```
//!
//! If you add `#[weight(0)]` to a variant, the variant does not appear, so you can use a type in that variant that cannot be used as `Arbitrary`.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Debug)]
//! struct NotArbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! enum TestInput {
//!     A,
//!
//!     #[allow(dead_code)]
//!     #[weight(0)] // Removing this `#[weight(0)]` will cause a compile error.
//!     B(NotArbitrary),
//! }
//! ```
//!
//! ## `#[map]`
//!
//! Instead of using `prop_map` in `#[strategy(...)]`, `#[map(...)]` can be used.
//!
//! The following codes mean the same thing.
//!
//! ```rust
//! use proptest::arbitrary::any;
//! use proptest::strategy::Strategy;
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput1 {
//!     #[strategy(any::<u32>().prop_map(|x| x + 1))]
//!     x: u32,
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput2 {
//!     #[strategy(any::<u32>())]
//!     #[map(|x| x + 1)]
//!     x: u32,
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput3 {
//!     #[map(|x: u32| x + 1)]
//!     x: u32,
//! }
//! ```
//!
//! References to other fields in the function applied to `prop_map` or `#[map(...)]` will generate different strategies.
//!
//! Referencing another field in `#[strategy(...)]` will expand it to `prop_flat_map`, even if it is in `prop_map`.
//!
//! ```rust
//! use proptest::arbitrary::any;
//! use proptest::strategy::{Just, Strategy};
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct T1 {
//!     x: u32,
//!
//!     #[strategy(any::<u32>().prop_map(move |y| #x + y))]
//!     y: u32,
//! }
//! // The code above generates the following strategy.
//! let t1 = any::<u32>()
//!     .prop_flat_map(|x| (Just(x), any::<u32>().prop_map(move |y| x + y)))
//!     .prop_map(|(x, y)| T1 { x, y });
//! ```
//!
//! On the other hand, if you refer to another field in `#[map]`, it will expand to `prop_map`.
//!
//! ```rust
//! use proptest::arbitrary::any;
//! use proptest::strategy::Strategy;
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct T2 {
//!     x: u32,
//!
//!     #[map(|y: u32| #x + y)]
//!     y: u32,
//! }
//! // The code above generates the following strategy.
//! let t2 = (any::<u32>(), any::<u32>()).prop_map(|(x, y)| T2 { x, y });
//! ```
//!
//! If the input and output types of the function specified in `#[map]` are different, the value type of the strategy set in `#[strategy]` is the type of the function's input, not the type of the field.
//!
//! ```rust
//! use proptest::arbitrary::any;
//! use proptest::sample::Index;
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct T1 {
//!     #[strategy(any::<Index>())]
//!     #[map(|i: Index| i.index(10))]
//!     x: usize,
//! }
//!
//! // `#[strategy(any::<Index>())]` can be omitted.
//! #[derive(Arbitrary, Debug)]
//! struct T2 {
//!     #[map(|i: Index| i.index(10))]
//!     x: usize,
//! }
//! ```
//!
//! ## `#[filter]`
//!
//! By adding `#[filter]` , you can limit the values generated.
//!
//! In the following examples, x is an even number.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     #[filter(#x % 2 == 0)]
//!     x: u32,
//! }
//! ```
//!
//! You can also use multiple variables in a predicate.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! #[filter((#x + #y) % 2 == 0)]
//! struct T1 {
//!     x: u32,
//!     y: u32,
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! struct T2 {
//!     x: u32,
//!     #[filter((#x + #y) % 2 == 0)]
//!     y: u32,
//! }
//! ```
//!
//! You can use the value of a structure or enum in the filter by using `#self`.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! #[filter((#self.x + #self.y) % 2 == 0)]
//! struct TestInput {
//!     x: u32,
//!     y: u32,
//! }
//! ```
//!
//! If the expression specified for `#[filter]` does not contain a variable named by appending # to its own field name, the expression is treated as a predicate function, rather than an expression that returns a bool.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     #[filter(is_even)]
//!     x: u32,
//! }
//! fn is_even(x: &u32) -> bool {
//!     x % 2 == 0
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! struct T2 {
//!     a: u32,
//!
//!     // Since `#a` exists but `#b` does not, it is treated as a predicate function.
//!     #[filter(|&x| x > #a)]
//!     b: u32,
//! }
//! ```
//!
//! Similarly, an expression that does not contain `#self` in the `#[filter(...)]` that it attaches to a type is treated as a predicate function.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! #[filter(is_even)]
//! struct T {
//!     x: u32,
//! }
//! fn is_even(t: &T) -> bool {
//!     t.x % 2 == 0
//! }
//! ```
//!
//! You can specify a filter name by passing two arguments to `#[filter]`.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     #[filter("x is even", #x % 2 == 0)]
//!     x: u32,
//! }
//! ```
//!
//! ## `#[by_ref]`
//!
//! By default, if you use a variable with `#[strategy]`, `#[any]`, `#[map]` or `#[filter]` with `#` attached to it, the cloned value is set.
//!
//! Adding `#[by_ref]` to the field makes it use the reference instead of the cloned value.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInput {
//!     #[by_ref]
//!     #[strategy(1..10u32)]
//!     x: u32,
//!
//!     #[strategy(0..*#x)]
//!     y: u32,
//! }
//! ```
//!
//! ## `#[arbitrary]`
//!
//! ### `#[arbitrary(args = T)]`
//!
//! Specifies the type of `Arbitrary::Parameters`.
//!
//! You can use the `Rc` value of this type in `#[strategy]`, `#[any]`, or `#[filter]` with the variable name `args`.
//!
//! ```rust
//! use test_strategy::Arbitrary;
//!
//! #[derive(Debug, Default)]
//! struct TestInputArgs {
//!     x_max: u32,
//! }
//!
//! #[derive(Arbitrary, Debug)]
//! #[arbitrary(args = TestInputArgs)]
//! struct TestInput {
//!     #[strategy(0..=args.x_max)]
//!     x: u32,
//! }
//! ```
//!
//! ### `#[arbitrary(bound(T1, T2, ..))]`
//!
//! By default, if the type of field for which `#[strategy]` is not specified contains a generic parameter, that type is set to trait bounds.
//!
//! Therefore, the following `TestInputA` and `TestInputB` are equivalent.
//!
//! ```rust
//! use proptest::{
//!     arbitrary::any, arbitrary::Arbitrary, strategy::BoxedStrategy, strategy::Strategy,
//! };
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug)]
//! struct TestInputA<T> {
//!     x: T,
//! }
//!
//! #[derive(Debug)]
//! struct TestInputB<T> {
//!     x: T,
//! }
//! impl<T: Arbitrary + 'static> Arbitrary for TestInputB<T> {
//!     type Parameters = ();
//!     type Strategy = BoxedStrategy<Self>;
//!
//!     fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
//!         any::<T>().prop_map(|x| Self { x }).boxed()
//!     }
//! }
//! ```
//!
//! Types of fields with `#[strategy]` do not set trait bounds automatically, so you need to set trait bound manually with `#[arbitrary(bound(T))]`.
//!
//! ```rust
//! use proptest::arbitrary::any_with;
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug, PartialEq)]
//! #[arbitrary(bound(T))]
//! struct TestInput<T> {
//!     #[strategy(any_with::<T>(Default::default()))]
//!     x: T,
//! }
//! ```
//!
//! You can also specify where predicate instead of type.
//!
//! ```rust
//! use proptest::arbitrary::{any_with, Arbitrary};
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug, PartialEq)]
//! #[arbitrary(bound(T : Arbitrary + 'static))]
//! struct TestInput<T> {
//!     #[strategy(any_with::<T>(Default::default()))]
//!     x: T,
//! }
//! ```
//!
//! `..` means automatically generated trait bounds.
//!
//! The following example uses a manually specified trait bounds in addition to the automatically generated trait bounds.
//!
//! ```rust
//! use proptest::arbitrary::any_with;
//! use test_strategy::Arbitrary;
//!
//! #[derive(Arbitrary, Debug, PartialEq)]
//! #[arbitrary(bound(T1, ..))]
//! struct TestInput<T1, T2> {
//!     #[strategy(any_with::<T1>(Default::default()))]
//!     x: T1,
//!
//!     y: T2,
//! }
//! ```
//!
//! ### `#[arbitrary(dump)]`
//!
//! Causes a compile error and outputs the code generated by `#[derive(Arbitrary)]` as an error message.
//!
//! ## `#[proptest]`
//!
//! `#[proptest]` is the attribute used instead of `#[test]` when defining a property test.
//!
//! The following example defines a test that takes a variety of integers as input.
//!
//! ```rust
//! use test_strategy::proptest;
//!
//! #[proptest]
//! fn my_test(_input: i32) {
//!     // ...
//! }
//! ```
//!
//! You can add `#[strategy]`, `#[any]`, `#[filter]`, `#[by_ref]` to the parameter of the function with `# [proptest]`.
//!
//! ```rust
//! use test_strategy::proptest;
//!
//! #[proptest]
//! fn my_test2(#[strategy(10..20)] _input: i32) {
//!     // ...
//! }
//! ```
//!
//! You can change the configuration of a property test by setting the argument of `#[proptest]` attribute to a value of `proptest::prelude::ProptestConfig` type.
//!
//! ```rust
//! use proptest::prelude::ProptestConfig;
//! use test_strategy::proptest;
//!
//!
//! #[proptest(ProptestConfig { cases : 1000, ..ProptestConfig::default() })]
//! fn my_test_with_config(_input: i32) {
//!     // ...
//! }
//! ```
//!
//! As with `#[any]`, you can also set only the value of the field to be changed from the default value.
//!
//! The example below is equivalent to the one above.
//!
//! ```rust
//! use proptest::prelude::ProptestConfig;
//! use test_strategy::proptest;
//!
//! #[proptest(ProptestConfig::default(), cases = 1000)]
//! fn my_test_with_config_2(_input: i32) {
//!     // ...
//! }
//!
//! #[proptest(cases = 1000)]
//! fn my_test_with_config_3(_input: i32) {
//!     // ...
//! }
//! ```
//!
//! ### `#[proptest(async = ...)]`
//!
//! Async functions can be tested by setting `async = ...` to the argument of `#[proptest]`.
//!
//! The following values are allowed after `async =`.
//! The value specifies the asynchronous runtime used for the test.
//!
//! - "tokio"
//!
//! ```toml
//! [dev-dependencies]
//! test-strategy = "0.3"
//! proptest = "1.1.0"
//! tokio = { version = "1.28.1", features = ["rt-multi-thread"] }
//! ```
//!
//! ```rust
//! use test_strategy::proptest;
//! use proptest::prop_assert;
//!
//! #[proptest(async = "tokio")]
//! async fn my_test_async() {
//!     async { }.await;
//!     prop_assert!(true);
//! }
//! ```
//!
//! ### `#[proptest(dump)]`
//!
//! You can use `#[proptest(dump)]` and output the code generated by `#[proptest]` as an compile error message.
//!
//! ```compile_fail
//! #[proptest(dump)]
//! fn my_test(_input: i32) {
//!     // ...
//! }
//! ```
// #![include_doc("../README.md", end("## License"))]

extern crate proc_macro;

#[macro_use]
mod syn_utils;
mod arbitrary;
mod bound;
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
    attributes(arbitrary, strategy, any, map, filter, weight, by_ref)
)]
pub fn derive_arbitrary(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    into_macro_output(arbitrary::derive_arbitrary(input))
}
