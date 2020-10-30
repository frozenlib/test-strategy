use test_strategy::Arbitrary;
struct TestArgs {
    x_max: u32,
}
#[derive(Arbitrary, Debug, PartialEq)]
#[arbitrary(args = TestArgs)]
struct TestStruct {
    #[strategy(0..args.x_max)]
    x: u32,
}

fn main() {}
