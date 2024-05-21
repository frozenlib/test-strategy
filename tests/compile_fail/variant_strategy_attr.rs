use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug)]
enum X {
    #[strategy(0..10usize)]
    A(usize),
}

fn main() {}
