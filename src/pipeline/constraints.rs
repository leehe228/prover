// Developed by Hoeun Lee, AIDAS Lab, Seoul National University
// Add Query Constraints to QED Prover

use z3::{ast::{Ast, Bool, Dynamic}, Context, Solver};
use crate::pipeline::shared::DataType;
use itertools::Itertools;

/// Builds a universally quantified formula asserting that two relations are equal.
/// ∀ t. r1(t) = r2(t)
pub fn rel_eq<'c>(ctx: &'c Context, r1: &Dynamic<'c>, r2: &Dynamic<'c>) -> Bool<'c> {
    // Assume that a tuple sort "Tuple" exists in the context.
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t = Dynamic::new_const(ctx, "t", &tuple_sort);
    let r1_t = r1.apply(&[&t]);
    let r2_t = r2.apply(&[&t]);
    let eq = r1_t._eq(&r2_t);
    Bool::forall_const(ctx, &[&t], &[], &eq)
}

/// Builds a universally quantified formula asserting that two attribute functions are equal.
/// ∀ t. a1(t) = a2(t)
pub fn attrs_eq<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t = Dynamic::new_const(ctx, "t", &tuple_sort);
    let a1_t = a1.apply(&[&t]);
    let a2_t = a2.apply(&[&t]);
    let eq = a1_t._eq(&a2_t);
    Bool::forall_const(ctx, &[&t], &[], &eq)
}

/// Builds a universally quantified formula asserting that two predicates are equivalent.
/// ∀ t. p1(t) = p2(t)
pub fn pred_eq<'c>(ctx: &'c Context, p1: &Dynamic<'c>, p2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t = Dynamic::new_const(ctx, "t", &tuple_sort);
    let p1_t = p1.apply(&[&t]);
    let p2_t = p2.apply(&[&t]);
    let eq = p1_t._eq(&p2_t);
    Bool::forall_const(ctx, &[&t], &[], &eq)
}

/// Builds a universally quantified formula asserting sub-attribute composition:
/// ∀ t. a1(t) = a1(a2(t))
pub fn sub_attr<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t = Dynamic::new_const(ctx, "t", &tuple_sort);
    let a1_t = a1.apply(&[&t]);
    let a2_t = a2.apply(&[&t]);
    let a1_a2_t = a1.apply(&[&a2_t]);
    let eq = a1_t._eq(&a1_a2_t);
    Bool::forall_const(ctx, &[&t], &[], &eq)
}

/// Builds a universally quantified formula for referential attribute constraint:
/// ∀ t1. (r1(t1) > 0 ∧ ¬IsNull(a1(t1))) ⇒ ∃ t2. (r2(t2) > 0 ∧ ¬IsNull(a2(t2)) ∧ [a1(t1)=a2(t2)])
pub fn ref_attr<'c>(ctx: &'c Context, r1: &Dynamic<'c>, a1: &Dynamic<'c>, r2: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t1 = Dynamic::new_const(ctx, "t1", &tuple_sort);
    let t2 = Dynamic::new_const(ctx, "t2", &tuple_sort);
    let r1_t1 = r1.apply(&[&t1]);
    let r2_t2 = r2.apply(&[&t2]);
    let cond = Bool::and(ctx, &[
        &r1_t1.gt(&Dynamic::from_i64(ctx, 0)),
        &Bool::not(&is_null(ctx, &a1.apply(&[&t1])))
    ]);
    let eq = a1.apply(&[&t1])._eq(&a2.apply(&[&t2]));
    let exists_t2 = Bool::exists_const(ctx, &[&t2], &[], &Bool::and(ctx, &[
        &r2_t2.gt(&Dynamic::from_i64(ctx, 0)),
        &Bool::not(&is_null(ctx, &a2.apply(&[&t2]))),
        &eq,
    ]));
    let implication = Bool::implies(ctx, &cond, &exists_t2);
    Bool::forall_const(ctx, &[&t1], &[], &implication)
}

/// Builds a constraint that enforces uniqueness on relation r by attribute a.
/// (∀ t. r(t) ≤ 1) ∧ (∀ t, t'. (r(t)>0 ∧ r(t')>0 ∧ a(t)=a(t')) ⇒ t=t')
pub fn unique<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t = Dynamic::new_const(ctx, "t", &tuple_sort);
    let t_prime = Dynamic::new_const(ctx, "t_prime", &tuple_sort);
    let r_t = r.apply(&[&t]);
    let r_tprime = r.apply(&[&t_prime]);
    let a_t = a.apply(&[&t]);
    let a_tprime = a.apply(&[&t_prime]);
    let part1 = Bool::forall_const(ctx, &[&t], &[], &r_t.le(&Dynamic::from_i64(ctx, 1)));
    let part2_body = Bool::implies(ctx,
                                   &Bool::and(ctx, &[
                                       &r_t.gt(&Dynamic::from_i64(ctx, 0)),
                                       &r_tprime.gt(&Dynamic::from_i64(ctx, 0)),
                                       &a_t._eq(&a_tprime)
                                   ]),
                                   &t._eq(&t_prime)
    );
    let part2 = Bool::forall_const(ctx, &[&t, &t_prime], &[], &part2_body);
    Bool::and(ctx, &[&part1, &part2])
}

/// Builds a non-null constraint: ∀ t. (r(t)>0 ⇒ ¬IsNull(a(t)))
pub fn not_null<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx.named_sort("Tuple").expect("Tuple sort must be defined");
    let t = Dynamic::new_const(ctx, "t", &tuple_sort);
    let r_t = r.apply(&[&t]);
    let a_t = a.apply(&[&t]);
    let cond = Bool::implies(ctx, &r_t.gt(&Dynamic::from_i64(ctx, 0)), &Bool::not(&is_null(ctx, &a_t)));
    Bool::forall_const(ctx, &[&t], &[], &cond)
}

/// A helper function to check if a given expression equals the distinguished NULL value.
/// This function must be adapted to the Q-expression encoding of NULL.
pub fn is_null<'c>(ctx: &'c Context, expr: &Dynamic<'c>) -> Bool<'c> {
    let null_const = Dynamic::fresh_const(ctx, "null", &expr.get_sort());
    expr._eq(&null_const)
}
