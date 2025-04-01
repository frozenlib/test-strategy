use ::std::result::Result;
use std::{future::Future, rc::Rc};

use ::proptest::test_runner::TestCaseError;
use proptest::{prelude::ProptestConfig, prop_assert};
use test_strategy::proptest;
use tokio::task::yield_now;

use googletest::expect_that;
use googletest::gtest;
use googletest::matchers::*;
use googletest::verify_that;

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

struct NotImplError0;
struct NotImplError1;

#[derive(Debug)]
struct CustomError(#[allow(dead_code)] TestCaseError);

impl CustomError {
    fn new() -> Self {
        CustomError(TestCaseError::fail("Custom"))
    }
}

impl std::error::Error for CustomError {}
impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CustomError")
    }
}
impl From<TestCaseError> for CustomError {
    fn from(e: TestCaseError) -> Self {
        CustomError(e)
    }
}
impl From<NotImplError0> for CustomError {
    fn from(_: NotImplError0) -> Self {
        CustomError(TestCaseError::fail("Custom"))
    }
}
impl From<NotImplError1> for CustomError {
    fn from(_: NotImplError1) -> Self {
        CustomError(TestCaseError::fail("Custom"))
    }
}

macro_rules! prop_assert_custom {
    ($cond:expr) => {
        prop_assert_custom!($cond, concat!("assertion failed: ", stringify!($cond)))
    };
    ($cond:expr, $($fmt:tt)*) => {
        if !$cond {
            let message = format!($($fmt)*);
            let message = format!("{} at {}:{}", message, file!(), line!());
            ::core::result::Result::Err(::proptest::test_runner::TestCaseError::fail(message))?;
        }
    };
}

#[proptest]
fn custom_error_ok(#[strategy(1..10u8)] x: u8) -> Result<(), CustomError> {
    prop_assert_custom!(x < 10);
    not_impl_error_ok()?;
    Ok(())
}
#[proptest(async = "tokio")]
async fn custom_error_ok_async(#[strategy(1..10u8)] x: u8) -> Result<(), CustomError> {
    prop_assert_custom!(x < 10);
    not_impl_error_ok()?;
    yield_now().await;
    Ok(())
}

#[should_panic]
#[proptest]
fn custom_error_prop_assesrt_fail(#[strategy(1..10u8)] x: u8) -> Result<(), CustomError> {
    prop_assert_custom!(x >= 10);
    Ok(())
}

#[proptest]
#[should_panic]
fn custom_error_err(#[strategy(1..10u8)] x: u8) -> Result<(), CustomError> {
    prop_assert_custom!(x < 10);
    not_impl_error_err()?;
    Ok(())
}

#[proptest(async = "tokio")]
#[should_panic]
async fn custom_error_err_async(#[strategy(1..10u8)] x: u8) -> Result<(), CustomError> {
    prop_assert_custom!(x < 10);
    not_impl_error_err()?;
    yield_now().await;
    Ok(())
}

#[proptest]
fn custom_error_ok_2(#[strategy(1..10u8)] x: u8) -> Result<(), CustomError> {
    prop_assert_custom!(x < 10);
    not_impl_error_ok()?;
    not_impl_error_ok_1()?;
    Ok(())
}

fn not_impl_error_ok() -> Result<(), NotImplError0> {
    Ok(())
}
fn not_impl_error_err() -> Result<(), NotImplError0> {
    Err(NotImplError0)
}

fn not_impl_error_ok_1() -> Result<(), NotImplError1> {
    Ok(())
}

macro_rules! prop_assert_anyhow {
    ($cond:expr) => {
        prop_assert_anyhow!($cond, concat!("assertion failed: ", stringify!($cond)))
    };
    ($cond:expr, $($fmt:tt)*) => {
        if !$cond {
            anyhow::bail!("{} at {}:{}", format!($($fmt)*), file!(), line!());
        }
    };
}

#[proptest]
fn anyhow_result_ok(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x < 10);
    Ok(())
}

#[proptest(async = "tokio")]
async fn anyhow_result_ok_async(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x < 10);
    yield_now().await;
    Ok(())
}

#[proptest]
#[should_panic]
fn anyhow_result_prop_assert_fail(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x >= 10);
    Ok(())
}

#[proptest(async = "tokio")]
#[should_panic]
async fn anyhow_result_prop_assert_fail_async(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x >= 10);
    yield_now().await;
    Ok(())
}

#[proptest]
#[should_panic]
fn anyhow_result_err(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x < 10);
    Err(CustomError::new())?;
    Ok(())
}

#[proptest(async = "tokio")]
#[should_panic]
async fn anyhow_result_err_async(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x < 10);
    Err(CustomError::new())?;
    yield_now().await;
    Ok(())
}

#[proptest]
#[should_panic]
fn anyhow_result_bail(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x < 10);
    anyhow::bail!("error");
}

#[proptest(async = "tokio")]
#[should_panic]
async fn anyhow_result_bail_async(#[strategy(1..10u8)] x: u8) -> anyhow::Result<()> {
    prop_assert_anyhow!(x < 10);
    yield_now().await;
    anyhow::bail!("error");
}

#[proptest]
#[gtest]
fn googletest_result(#[strategy(1..10u8)] x: u8) -> googletest::Result<()> {
    expect_that!(x, ge(1));
    verify_that!(x, lt(10))
}
