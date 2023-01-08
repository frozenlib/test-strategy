use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq, Clone)]
enum TestEnum {
    #[filter(Self::is_match)]
    A {
        x: i32,
        y: i32,
    },
    B(i32),
}

impl TestEnum {
    fn is_match(self) -> bool {
        true
    }
}

fn main() {}
