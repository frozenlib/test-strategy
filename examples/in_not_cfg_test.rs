fn main() {}

#[test_strategy::proptest]
fn arg(x: u8) {}

#[test_strategy::proptest(cases = 100)]
fn arg_and_config(x: u8) {}
