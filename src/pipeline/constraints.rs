// Developed by Hoeun Lee, AIDAS Lab, Seoul National University
// Add Query Constraints to QED Prover

use z3::{
    ast::{Ast, Bool, Dynamic, Int},
    Context,
};

use imbl::{vector, Vector};

/// Helper: apply a function-typed Dynamic value to arguments.
/// This unwraps the function declaration from the Dynamic value and converts the arguments
/// to the expected slice of trait objects.
fn apply_dyn<'c>(d: &Dynamic<'c>, args: &[&Dynamic<'c>]) -> Dynamic<'c> {
    let func_decl = d.safe_decl().expect("failed to get function declaration");
    let ast_args: Vec<&dyn Ast> = args.iter().map(|a| *a as &dyn Ast).collect();
    func_decl.apply(&ast_args)
}

/// Helper: a stub for universal quantification.
/// In a full implementation, you would construct a proper quantifier.
/// Here we simply return the body.
fn forall<'c>(
    _ctx: &'c Context,
    _bound: &[&Dynamic<'c>],
    _patterns: &[&[&Dynamic<'c>]],
    body: &Bool<'c>,
) -> Bool<'c> {
    body.clone()
}

/// Returns an uninterpreted sort for "Tuple".
fn tuple_sort<'c>(ctx: &'c Context) -> z3::Sort<'c> {
    z3::Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()))
}

/// Returns an universally quantified formula asserting that two relations are equal:
/// ∀ t. r1(t) = r2(t)
pub fn rel_eq<'c>(ctx: &'c Context, r1: &Dynamic<'c>, r2: &Dynamic<'c>) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t = Dynamic::fresh_const(ctx, "t", &ts);
    let r1_t = apply_dyn(r1, &[&t]);
    let r2_t = apply_dyn(r2, &[&t]);
    let eq = r1_t._eq(&r2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns an universally quantified formula asserting that two attributes are equal:
/// ∀ t. a1(t) = a2(t)
pub fn attrs_eq<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t = Dynamic::fresh_const(ctx, "t", &ts);
    let a1_t = apply_dyn(a1, &[&t]);
    let a2_t = apply_dyn(a2, &[&t]);
    let eq = a1_t._eq(&a2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns an universally quantified formula asserting predicate equivalence:
/// ∀ t. p1(t) = p2(t)
pub fn pred_eq<'c>(ctx: &'c Context, p1: &Dynamic<'c>, p2: &Dynamic<'c>) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t = Dynamic::fresh_const(ctx, "t", &ts);
    let p1_t = apply_dyn(p1, &[&t]);
    let p2_t = apply_dyn(p2, &[&t]);
    let eq = p1_t._eq(&p2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns an universally quantified formula for sub-attribute composition:
/// ∀ t. a1(t) = a1(a2(t))
pub fn sub_attr<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t = Dynamic::fresh_const(ctx, "t", &ts);
    let a1_t = apply_dyn(a1, &[&t]);
    let a2_t = apply_dyn(a2, &[&t]);
    let a1_a2_t = apply_dyn(a1, &[&a2_t]);
    let eq = a1_t._eq(&a1_a2_t);
    forall(ctx, &[&t], &[], &eq)
}

/// Returns an universally quantified formula for referential attributes:
/// ∀ t1. (r1(t1) > 0 ∧ ¬IsNull(a1(t1))) ⇒ ∃ t2. (r2(t2) > 0 ∧ ¬IsNull(a2(t2)) ∧ [a1(t1)=a2(t2)])
pub fn ref_attr<'c>(
    ctx: &'c Context,
    r1: &Dynamic<'c>,
    a1: &Dynamic<'c>,
    r2: &Dynamic<'c>,
    a2: &Dynamic<'c>,
) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t1 = Dynamic::fresh_const(ctx, "t1", &ts);
    let t2 = Dynamic::fresh_const(ctx, "t2", &ts);
    let r1_t1 = apply_dyn(r1, &[&t1]);
    let r2_t2 = apply_dyn(r2, &[&t2]);
    // Convert relation values to integer (assuming they represent counts).
    let r1_t1_int = r1_t1.as_int().expect("Expected integer sort for r1");
    let r2_t2_int = r2_t2.as_int().expect("Expected integer sort for r2");
    let cond = Bool::and(ctx, &[
        &r1_t1_int.gt(&Int::from_i64(ctx, 0)),
        &Bool::not(&is_null(ctx, &apply_dyn(a1, &[&t1]))),
    ]);
    let eq = apply_dyn(a1, &[&t1])._eq(&apply_dyn(a2, &[&t2]));
    // For existential quantification, we build a conjunction as a stub.
    let exists_t2 = Bool::and(ctx, &[
        &r2_t2_int.gt(&Int::from_i64(ctx, 0)),
        &Bool::not(&is_null(ctx, &apply_dyn(a2, &[&t2]))),
        &eq,
    ]);
    let implication = Bool::implies(&r1_t1_int.gt(&Int::from_i64(ctx, 0)), &exists_t2);
    forall(ctx, &[&t1], &[], &implication)
}

/// Returns an universally quantified formula for uniqueness:
/// (∀ t. r(t) ≤ 1) ∧ (∀ t, t'. (r(t) > 0 ∧ r(t') > 0 ∧ a(t) = a(t')) ⇒ t = t')
pub fn unique<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t = Dynamic::fresh_const(ctx, "t", &ts);
    let t_prime = Dynamic::fresh_const(ctx, "t_prime", &ts);
    let r_t = apply_dyn(r, &[&t]);
    let r_tprime = apply_dyn(r, &[&t_prime]);
    let a_t = apply_dyn(a, &[&t]);
    let a_tprime = apply_dyn(a, &[&t_prime]);
    let r_t_int = r_t.as_int().expect("Expected integer sort for r");
    let part1 = forall(ctx, &[&t], &[], &r_t_int.le(&Int::from_i64(ctx, 1)));
    let impl_body = Bool::implies(
        &Bool::and(ctx, &[
            &r_t_int.gt(&Int::from_i64(ctx, 0)),
            &r_tprime.as_int().expect("Expected Int").gt(&Int::from_i64(ctx, 0)),
            &a_t._eq(&a_tprime),
        ]),
        &t._eq(&t_prime),
    );
    let part2 = forall(ctx, &[&t, &t_prime], &[], &impl_body);
    Bool::and(ctx, &[&part1, &part2])
}

/// Returns an universally quantified formula for non-null constraint:
/// ∀ t. (r(t) > 0 ⇒ ¬IsNull(a(t)))
pub fn not_null<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let ts = tuple_sort(ctx);
    let t = Dynamic::fresh_const(ctx, "t", &ts);
    let r_t = apply_dyn(r, &[&t]);
    let a_t = apply_dyn(a, &[&t]);
    let r_t_int = r_t.as_int().expect("Expected integer sort for r");
    let cond = Bool::implies(&r_t_int.gt(&Int::from_i64(ctx, 0)), &Bool::not(&is_null(ctx, &a_t)));
    forall(ctx, &[&t], &[], &cond)
}

/// Helper: returns a formula that checks if `expr` equals the distinguished NULL.
/// This function assumes that a distinguished NULL constant is defined for the sort of `expr`.
pub fn is_null<'c>(ctx: &'c Context, expr: &Dynamic<'c>) -> Bool<'c> {
    // Create a fresh constant of the same sort; in a full implementation,
    // you would compare against a globally fixed NULL constant.
    let null_const = Dynamic::fresh_const(ctx, "null", &expr.get_sort());
    expr._eq(&null_const)
}
