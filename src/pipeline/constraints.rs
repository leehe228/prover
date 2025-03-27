// Developed by Hoeun Lee, AIDAS Lab, Seoul National University
// Add Query Constraints to QED Prover

use z3::{
    ast::{Ast, Bool, Dynamic, Quantifier},
    Context, Sort,
};

/// Creates a universally quantified formula.
/// Wraps the Quantifier::new_forall_const API.
fn forall_const<'c>(
    ctx: &'c Context,
    vars: &[&Dynamic<'c>],
    patterns: &[&[&Dynamic<'c>]],
    body: &Bool<'c>,
) -> Bool<'c> {
    Quantifier::new_forall_const(ctx, vars, patterns, body)
        .as_bool()
        .expect("Failed to create universal quantifier")
}

/// Creates an existentially quantified formula.
fn exists_const<'c>(
    ctx: &'c Context,
    vars: &[&Dynamic<'c>],
    patterns: &[&[&Dynamic<'c>]],
    body: &Bool<'c>,
) -> Bool<'c> {
    Quantifier::new_exists_const(ctx, vars, patterns, body)
        .as_bool()
        .expect("Failed to create existential quantifier")
}

/// Returns a universally quantified formula asserting that two relations are equal:
/// ∀ t. r1(t) = r2(t)
pub fn rel_eq<'c>(ctx: &'c Context, r1: &Dynamic<'c>, r2: &Dynamic<'c>) -> Bool<'c> {
    // Create an uninterpreted sort "Tuple" to serve as the domain.
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let r1_t = (*r1).apply(&[&t]);
    let r2_t = (*r2).apply(&[&t]);
    let eq = r1_t._eq(&r2_t);
    forall_const(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula asserting that two attributes are equal:
/// ∀ t. a1(t) = a2(t)
pub fn attrs_eq<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let a1_t = (*a1).apply(&[&t]);
    let a2_t = (*a2).apply(&[&t]);
    let eq = a1_t._eq(&a2_t);
    forall_const(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula asserting predicate equivalence:
/// ∀ t. p1(t) = p2(t)
pub fn pred_eq<'c>(ctx: &'c Context, p1: &Dynamic<'c>, p2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let p1_t = (*p1).apply(&[&t]);
    let p2_t = (*p2).apply(&[&t]);
    let eq = p1_t._eq(&p2_t);
    forall_const(ctx, &[&t], &[], &eq)
}

/// Returns a universally quantified formula for sub-attribute composition:
/// ∀ t. a1(t) = a1(a2(t))
pub fn sub_attr<'c>(ctx: &'c Context, a1: &Dynamic<'c>, a2: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let a1_t = (*a1).apply(&[&t]);
    let a1_a2_t = (*a1).apply(&[&(*a2).apply(&[&t])]);
    let eq = a1_t._eq(&a1_a2_t);
    forall_const(ctx, &[&t], &[], &eq)
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
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t1 = Dynamic::fresh_const(ctx, "t1", &tuple_sort);
    let t2 = Dynamic::fresh_const(ctx, "t2", &tuple_sort);
    let r1_t1 = (*r1).apply(&[&t1]);
    let r2_t2 = (*r2).apply(&[&t2]);

    // Use an Int constant 0 converted to Dynamic.
    let zero = z3::ast::Int::from_i64(ctx, 0).into();
    let cond = Bool::and(ctx, &[
        &r1_t1.gt(&zero),
        &Bool::not(&is_null(ctx, &(*a1).apply(&[&t1]))),
    ]);
    let eq = (*a1).apply(&[&t1])._eq(&(*a2).apply(&[&t2]));
    let exists_t2 = exists_const(ctx, &[&t2], &[], &Bool::and(ctx, &[
        &r2_t2.gt(&zero),
        &Bool::not(&is_null(ctx, &(*a2).apply(&[&t2]))),
        &eq,
    ]));
    // Note: Remove the extra context parameter from implies.
    let implication = Bool::implies(&cond, &exists_t2);
    forall_const(ctx, &[&t1], &[], &implication)
}

/// Returns a universally quantified formula for uniqueness:
/// (∀ t. r(t) ≤ 1) ∧ (∀ t, t'. (r(t) > 0 ∧ r(t') > 0 ∧ a(t) = a(t')) ⇒ t = t')
pub fn unique<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let t_prime = Dynamic::fresh_const(ctx, "t_prime", &tuple_sort);
    let r_t = (*r).apply(&[&t]);
    let r_tprime = (*r).apply(&[&t_prime]);
    let a_t = (*a).apply(&[&t]);
    let a_tprime = (*a).apply(&[&t_prime]);
    let part1 = forall_const(ctx, &[&t], &[], &r_t.le(&z3::ast::Int::from_i64(ctx, 1).into()));
    let part2 = forall_const(
        ctx,
        &[&t, &t_prime],
        &[],
        &Bool::implies(
            &Bool::and(ctx, &[
                &r_t.gt(&z3::ast::Int::from_i64(ctx, 0).into()),
                &r_tprime.gt(&z3::ast::Int::from_i64(ctx, 0).into()),
                &a_t._eq(&a_tprime),
            ]),
            &t._eq(&t_prime),
        ),
    );
    Bool::and(ctx, &[&part1, &part2])
}

/// Returns a universally quantified formula for non-null constraint:
/// ∀ t. (r(t) > 0 ⇒ ¬IsNull(a(t)))
pub fn not_null<'c>(ctx: &'c Context, r: &Dynamic<'c>, a: &Dynamic<'c>) -> Bool<'c> {
    let tuple_sort = Sort::uninterpreted(ctx, z3::Symbol::String("Tuple".to_string()));
    let t = Dynamic::fresh_const(ctx, "t", &tuple_sort);
    let r_t = (*r).apply(&[&t]);
    let a_t = (*a).apply(&[&t]);
    let cond = Bool::implies(&r_t.gt(&z3::ast::Int::from_i64(ctx, 0).into()), &Bool::not(&is_null(ctx, &a_t)));
    forall_const(ctx, &[&t], &[], &cond)
}

/// Helper: returns a formula that checks if `expr` equals the distinguished NULL.
/// This function assumes that a distinguished NULL constant is defined for the sort of `expr`.
pub fn is_null<'c>(ctx: &'c Context, expr: &Dynamic<'c>) -> Bool<'c> {
    let null_const = Dynamic::fresh_const(ctx, "null", &expr.get_sort());
    expr._eq(&null_const)
}
