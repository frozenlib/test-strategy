use proptest::{
    arbitrary::any, arbitrary::Arbitrary, strategy::Strategy, strategy::ValueTree,
    test_runner::TestRunner,
};
use std::fmt::Debug;

enum Op {
    Simplify,
    Complicate,
}

pub fn assert_arbitrary<T: Arbitrary + PartialEq>(e: impl Strategy<Value = T>) {
    assert_eq_strategy(any::<T>(), e);
}

pub fn assert_eq_strategy<T: Debug + PartialEq>(
    l: impl Strategy<Value = T>,
    r: impl Strategy<Value = T>,
) {
    let mut ops = vec![Op::Simplify];
    for _ in 0..100 {
        ops.push(Op::Simplify);
        ops.push(Op::Complicate);
    }
    assert_eq_strategy_ops(l, r, ops)
}

fn assert_eq_strategy_ops<T: Debug + PartialEq>(
    l: impl Strategy<Value = T>,
    r: impl Strategy<Value = T>,
    ops: Vec<Op>,
) {
    let mut l_runner = TestRunner::deterministic();
    let mut r_runner = TestRunner::deterministic();

    let mut l_tree = l.new_tree(&mut l_runner).unwrap();
    let mut r_tree = r.new_tree(&mut r_runner).unwrap();

    for op in ops {
        assert_eq!(l_tree.current(), r_tree.current());
        match op {
            Op::Simplify => assert_eq!(l_tree.simplify(), r_tree.simplify()),
            Op::Complicate => assert_eq!(l_tree.complicate(), r_tree.complicate()),
        }
    }
}
