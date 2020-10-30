use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug)]
struct TestStruct {
    #[strategy(0..10usize)]
    x: u8,
}

fn main() {}
