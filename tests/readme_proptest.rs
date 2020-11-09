use test_strategy::proptest;

#[proptest]
fn my_test(_input: i32) {
    // ...
}

#[proptest]
fn my_test2(#[strategy(10..20)] _input: i32) {
    // ...
}

use proptest::prelude::ProptestConfig;
#[proptest(ProptestConfig { cases : 1000, ..ProptestConfig::default() })]
fn my_test_with_config(_input: i32) {
    // ...
}

#[proptest(ProptestConfig::default(), cases = 1000)]
fn my_test_with_config_2(_input: i32) {
    // ...
}
#[proptest(cases = 1000)]
fn my_test_with_config_3(_input: i32) {
    // ...
}

// #[proptest]
// #[proptest_dump]
// fn my_test(_input: i32) {
//     // ...
// }
