use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug)]
struct TestStruct {
    #[strategy(1..#x)]
    x: u32,
}

fn main() {}
