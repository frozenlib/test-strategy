use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq, Clone)]
enum TestEnum {
    #[weight(1.1)]
    X,
    #[weight(2)]
    Y,
}

fn main() {}
