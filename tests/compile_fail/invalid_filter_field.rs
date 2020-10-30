use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq)]
struct TestStruct {
    #[strategy(1..10u32)]
    #[filter(bad_filter)]
    x: u32,
}
fn bad_filter() {}

fn main() {}
