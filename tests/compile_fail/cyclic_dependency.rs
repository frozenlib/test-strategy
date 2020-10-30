use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug)]
struct TestStruct {
    #[strategy(1..#y)]
    x: u32,

    #[strategy(1..#x)]
    y: u32,
}

fn main() {}
