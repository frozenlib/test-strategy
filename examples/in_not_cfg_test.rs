fn main() {}

#[test_strategy::proptest]
fn arg(#[allow(unused)] x: u8) {}

#[test_strategy::proptest(cases = 100)]
fn arg_and_config(#[allow(unused)] x: u8) {}
