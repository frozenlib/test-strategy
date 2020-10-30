use proptest::prelude::ProptestConfig;
use test_strategy::proptest;

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
fn with_strategy(#[strategy(2..10u32)] x: u32) {
    assert!(2 <= x);
    assert!(x < 10);
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
