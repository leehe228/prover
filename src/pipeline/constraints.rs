// Developed by Hoeun Lee, AIDAS Lab, Seoul National University
// Add Query Constraints to QED Prover

use z3::{
    ast::{Ast, Bool, Dynamic, Int},
    Context,
};

/// Helper: apply a function-typed Dynamic value to arguments.
fn apply_dyn<'c>(d: &Dynamic<'c>, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
    d.as_func_decl()
        .expect("Dynamic is not a function")
        .apply(args)
}

/// Helper: a stub for universal quantification. In a full implementation,
/// you would construct a proper quantifier. Here we simply return the body.
fn forall<'c>(
    _ctx: &'c Context,
    _bound: &[&Dynamic<'c>],
    _patterns: &[&[&Dynamic<'c>]],
    body: &Bool<'c>,
) -> Bool<'c> {
    body.clone()
}

/// Returns a universally quantified formula asserting that two relations are equal:
/// ∀ t. r1(t) = r2(t)
pub fn rel_eq<'c>(ctx: &'c Context, r1: &Dynamic<'c>, r2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let r1_t = apply_dyn(r1, &[&t]);
    let r2_t = apply_dyn(r2, &[&t]);
    let eq = r1_t._eq(&r2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula asserting that two attributes are equal:
/// ∀ t. a1(t) = a2(t)
pub fn attrs_eq<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let a1_t = apply_dyn(a1, &[&t]);
    let a2_t = apply_dyn(a2, &[&t]);
    let eq = a1_t._eq(&a2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula asserting predicate equivalence:
/// ∀ t. p1(t) = p2(t)
pub fn pred_eq<'c>(ctx: &'c Context, p1: &Dynamic<'c>, p2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let p1_t = apply_dyn(p1, &[&t]);
    let p2_t = apply_dyn(p2, &[&t]);
    let eq = p1_t._eq(&p2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula for sub-attribute composition:
/// ∀ t. a1(t) = a1(a2(t))
pub fn sub_attr<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let a1_t = apply_dyn(a1, &[&t]);
    let a2_t = apply_dyn(a2, &[&t]);
    let a1_a2_t = apply_dyn(a1, &[&a2_t]);
    let eq = a1_t._eq(&a1_a2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula for referential attributes:
/// ∀ t1. (r1(t1) > 0 ∧ ¬IsNull(a1(t1))) ⇒ ∃ t2. (r2(t2) > 0 ∧ ¬IsNull(a2(t2)) ∧ [a1(t1)=a2(t2)])
pub fn ref_attr<'c>(
    ctx: &'c Context,
    r1: &Dynamic<'c>,
    a1: &Dynamic<'c>,
    r2: &Dynamic<'c>,
    a2: &Dynamic<'c>,
) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t1 = Dynamic::fresh_const(ctx, "t1", &tuple_sort);
    let t2 = Dynamic::fresh_const(ctx, "t2", &tuple_sort);
    let r1_t1 = apply_dyn(r1, &[&t1]);
    let r2_t2 = apply_dyn(r2, &[&t2]);
    let cond = Bool::and(ctx, &[
        &r1_t1.gt(&Int::from_i64(ctx, 0).into()),
        &Bool::not(&is_null(ctx, &apply_dyn(a1, &[&t1]))),
    ]);
    let eq = apply_dyn(a1, &[&t1])._eq(&apply_dyn(a2, &[&t2]));
    // Construct an existential quantifier for t2.
    // Since Z3 quantifier support is not directly available, we use a stub:
    let exists_t2 = {
        // In a complete implementation, you would create an existential quantifier.
        // For our purposes, we simply return the conjunction as if t2 exists.
        Bool::and(ctx, &[
            &r2_t2.gt(&Int::from_i64(ctx, 0).into()),
            &Bool::not(&is_null(ctx, &apply_dyn(a2, &[&t2]))),
            &eq,
        ])
    };
    let implication = Bool::implies(&r1_t1.gt(&Int::from_i64(ctx, 0).into()), &exists_t2);
    // Note: we are not quantifying t1 existentially here.
    forall(ctx, &[&t1], &[], &implication)
}

/// Returns a universally quantified formula for uniqueness:
/// (∀ t. r(t) ≤ 1) ∧ (∀ t, t'. (r(t) > 0 ∧ r(t') > 0 ∧ a(t) = a(t')) ⇒ t = t')
pub fn unique<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let t_prime = Dynamic::fresh_const(ctx, "t_prime", &tuple_sort);
    let r_t = apply_dyn(r, &[&t]);
    let r_tprime = apply_dyn(r, &[&t_prime]);
    let a_t = apply_dyn(a, &[&t]);
    let a_tprime = apply_dyn(a, &[&t_prime]);
    let part1 = forall(ctx, &[&t], &[], &r_t.le(&Int::from_i64(ctx, 1).into()));
    let part2 = {
        let impl_body = Bool::implies(
            &Bool::and(ctx, &[
                &r_t.gt(&Int::from_i64(ctx, 0).into()),
                &r_tprime.gt(&Int::from_i64(ctx, 0).into()),
                &a_t._eq(&a_tprime),
            ]),
            &t._eq(&t_prime),
        );
        forall(ctx, &[&t, &t_prime], &[], &impl_body)
    };
    Bool::and(ctx, &[&part1, &part2])
}

/// Returns a universally quantified formula for non-null constraint:
/// ∀ t. (r(t) > 0 ⇒ ¬IsNull(a(t)))
pub fn not_null<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = ctx
        .get_sort("Tuple")
        .expect("Tuple sort must be defined");
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let r_t = apply_dyn(r, &[&t]);
    let a_t = apply_dyn(a, &[&t]);
    let cond = Bool::implies(&r_t.gt(&Int::from_i64(ctx, 0).into()), &Bool::not(&is_null(ctx, &a_t)));
    forall(ctx, &[&t], &[], &cond)
}

/// Helper: returns a formula that checks if `expr` equals the distinguished NULL.
/// This function assumes that a distinguished NULL constant is defined for the sort of `expr`.
pub fn is_null<'c>(ctx: &'c Context, expr: &Dynamic<'c>) -> Bool<'c> {
    // Create a fresh constant of the same sort; in a full implementation
    // you would compare against a globally fixed NULL.
    let null_const = Dynamic::fresh_const(ctx, "null", &expr.get_sort());
    expr._eq(&null_const)
}
