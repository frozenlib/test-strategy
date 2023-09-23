use test_strategy::Arbitrary;

// A compile error needs to occur on line 6, not on line 4.
#[derive(Debug, Arbitrary)]
struct X {
    #[strategy((0u8..10u8))]
    x: u32,
}

fn main() {}
