use test_strategy::Arbitrary;

#[derive(Arbitrary, Debug)]
struct TestInput {
    #[strategy(1..10u32)]
    x: u32,

    #[strategy(0..*#x)]
    y: u32,
}

fn main() {}
