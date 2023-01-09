use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq)]
struct TestStruct {
    #[filter(#x)]
    x: u32,
}
fn bad_filter() {}

fn main() {}
