use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq, Clone)]
#[filter(#x > #y)]
enum TestEnum {
    A { x: i32, y: i32 },
    B(i32),
}

fn main() {}
