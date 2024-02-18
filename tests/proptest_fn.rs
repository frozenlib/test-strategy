use ::std::result::Result;
use std::{future::Future, rc::Rc};

use ::proptest::test_runner::TestCaseError;
use proptest::{prelude::ProptestConfig, prop_assert};
use test_strategy::proptest;
use tokio::task::yield_now;

#[proptest]
fn example(_x: u32, #[strategy(1..10u32)] y: u32, #[strategy(0..#y)] z: u32) {
    assert!(1 <= y);
    assert!(y < 10);
    assert!(z <= y);
}

#[proptest]
fn param_x1(_x: u32) {}

#[proptest]
fn param_x2(_x: u32, _y: u32) {}

#[proptest]
fn param_mut(mut _x: u32) {
    _x = 0;
}
#[proptest]
fn param_mut_x2(mut _x: u32, mut _y: u32) {
    _x = 0;
    _y = 0;
}

#[proptest]
fn with_strategy(#[strategy(2..10u32)] x: u32) {
    assert!(2 <= x);
    assert!(x < 10);
}

#[proptest]
fn with_map(
    #[strategy(2..10u32)]
    #[map(|x| x + 2)]
    x: u32,
) {
    assert!(4 <= x);
    assert!(x < 12);
}

#[proptest(ProptestConfig { timeout: 3, ..ProptestConfig::default() })]
#[should_panic]
fn config_expr() {
    std::thread::sleep(std::time::Duration::from_millis(30));
}

#[proptest(timeout = 3)]
#[should_panic]
fn config_field() {
    std::thread::sleep(std::time::Duration::from_millis(30));
}

#[proptest(ProptestConfig::default(), timeout = 3)]
#[should_panic]
fn config_expr_and_field() {
    std::thread::sleep(std::time::Duration::from_millis(30));
}

#[proptest(async = "tokio")]
async fn tokio_test() {
    tokio::task::spawn(async {}).await.unwrap()
}

#[proptest(async = "tokio")]
async fn tokio_test_no_copy_arg(#[strategy("a+")] s: String) {
    prop_assert!(s.contains('a'));
}

#[proptest(async = "tokio")]
async fn tokio_test_prop_assert() {
    prop_assert!(true);
}

#[should_panic]
#[proptest(async = "tokio")]
async fn tokio_test_prop_assert_false() {
    prop_assert!(false);
}

fn tokio_ct(future: impl Future<Output = Result<(), TestCaseError>>) -> Result<(), TestCaseError> {
    tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap()
        .block_on(future)
}

#[proptest(async = tokio_ct)]
async fn async_expr() {}

#[proptest(async = tokio_ct)]
async fn async_expr_non_send() {
    let x = Rc::new(0);
    yield_now().await;
    drop(x);
}

#[proptest(async = tokio_ct)]
async fn async_expr_no_copy_arg(#[strategy("a+")] s: String) {
    prop_assert!(s.contains('a'));
}

#[proptest(async = tokio_ct)]
async fn async_expr_test_prop_assert() {
    prop_assert!(true);
}

#[should_panic]
#[proptest(async = tokio_ct)]
async fn async_expr_test_prop_assert_false() {
    prop_assert!(false);
}
