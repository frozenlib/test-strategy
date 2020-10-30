use test_strategy::Arbitrary;
#[derive(Arbitrary, Debug, PartialEq, Clone)]
enum WeightAttrMoreArg {
    #[weight(1, 2)]
    X,
    Y,
}

fn main() {}
