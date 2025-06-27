use proptest::{
    arbitrary::any, arbitrary::Arbitrary, strategy::Strategy, strategy::ValueTree,
    test_runner::TestRunner,
};
use std::fmt::Debug;

enum Op {
    Simplify,
    Complicate,
}

#[track_caller]
pub fn assert_arbitrary<T: Arbitrary + PartialEq>(e: impl Strategy<Value = T>) {
    assert_eq_strategy(any::<T>(), e);
}

#[track_caller]
pub fn assert_eq_strategy<T: Debug + PartialEq>(
    l: impl Strategy<Value = T>,
    r: impl Strategy<Value = T>,
) {
    let mut ops = vec![Op::Simplify];
    for _ in 0..1000 {
        ops.push(Op::Simplify);
        ops.push(Op::Complicate);
    }
    assert_eq_strategy_ops(l, r, ops)
}

#[track_caller]
fn assert_eq_strategy_ops<T: Debug + PartialEq>(
    l: impl Strategy<Value = T>,
    r: impl Strategy<Value = T>,
    ops: Vec<Op>,
) {
    let mut l_runner = TestRunner::deterministic();
    let mut r_runner = TestRunner::deterministic();

    let mut r_tree = r
        .new_tree(&mut r_runner)
        .unwrap_or_else(|e| panic!("r.new_tree failed: {e:?}"));
    let mut l_tree = l
        .new_tree(&mut l_runner)
        .unwrap_or_else(|e| panic!("l.new_tree failed: {e:?}"));

    let mut step = 0;
    for op in ops {
        let l_value = l_tree.current();
        let r_value = r_tree.current();
        assert_eq!(l_value, r_value, "value: {step}");
        step += 1;
        match op {
            Op::Simplify => assert_eq!(l_tree.simplify(), r_tree.simplify(), "step: {step}"),
            Op::Complicate => assert_eq!(l_tree.complicate(), r_tree.complicate(), "step: {step}"),
        }
    }
}
