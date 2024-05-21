use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug)]
enum X {
    #[any]
    A,
}

fn main() {}
