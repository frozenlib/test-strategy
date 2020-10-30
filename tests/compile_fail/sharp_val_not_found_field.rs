use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq)]
struct TestStruct {
    #[strategy(0..#y)]
    x: u32,
}

fn main() {}
