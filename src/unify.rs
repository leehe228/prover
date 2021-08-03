use itertools::{Either, Itertools};
use scopeguard::defer;
use z3::ast::{Dynamic, Int, Ast, Bool, Real, exists_const, String as Str};
use z3::*;

use crate::evaluate::shared::{Application, Entry, Env, DataType};
use crate::evaluate::stable;
use crate::evaluate::stable::{Expr, Predicate, Relation};
use crate::unify::null::Nullable;
use std::collections::HashMap;

type Agg = (String, Relation);

fn trans_expr<'a>(ctx: &'a Context, expr: Expr, env: &Env<Dynamic<'a>>, aggs: &mut HashMap<Agg, Dynamic<'a>>) -> Dynamic<'a> {
	match expr {
		Expr::Var(v) => env.get(v).clone(),
		Expr::Op(op, args) => {
			if args.is_empty() {
				if let Ok(num) = op.parse() {
					Int::from_i64(ctx, num).into()
				} else {
					Str::from_str(ctx, op.as_str()).unwrap().into()
				}
			} else {
				if op == "CAST" {
					return trans_expr(ctx, args[0].clone(), env, aggs);
				}
				let args: Vec<_> = args.into_iter().map(|arg| trans_expr(ctx, arg, env, aggs).as_int().unwrap()).collect();
				match op.as_str() {
					"+" => Int::add(ctx, args.iter().collect::<Vec<_>>().as_slice()),
					"-" => Int::sub(ctx, args.iter().collect::<Vec<_>>().as_slice()),
					"*" => Int::mul(ctx, args.iter().collect::<Vec<_>>().as_slice()),
					"/" => args[0].div(&args[1]),
					"%" => args[0].modulo(&args[1]),
					op => {
						let domain: Vec<_> = args.iter().map(|_| Sort::int(ctx)).collect();
						let args: Vec<_> = args.iter().map(|int| Dynamic::from_ast(int)).collect();
						let f = FuncDecl::new(
							ctx,
							op,
							domain.iter().collect::<Vec<_>>().as_slice(),
							&Sort::int(ctx),
						);
						f.apply(args.iter().collect::<Vec<_>>().as_slice()).as_int().unwrap()
					},
				}.into()
			}
		},
		Expr::Agg(f, arg) => {
			// TODO: Correct type of fresh var
			aggs.entry((f, *arg)).or_insert_with(|| Int::fresh_const(ctx, "a").into()).clone()
		},
	}
}

fn trans_pred<'a>(ctx: &'a Context, pred: Predicate, env: &Env<Dynamic<'a>>, aggs: &mut HashMap<Agg, Dynamic<'a>>) -> Bool<'a> {
	match pred {
		Predicate::Eq(e1, e2) => trans_expr(ctx, e1, env, aggs)._eq(&trans_expr(ctx, e2, env, aggs)),
		Predicate::Pred(pred, args) => {
			if pred == "=" {
				let args: Vec<_> = args.into_iter().map(|arg| trans_expr(ctx, arg, env, aggs)).collect();
				return args[0]._eq(&args[1]);
			}
			let args: Vec<_> = args.into_iter().map(|arg| trans_expr(ctx, arg, env, aggs).as_int().unwrap()).collect();
			match pred.as_str() {
				">" => args[0].gt(&args[1]),
				"<" => args[0].lt(&args[1]),
				">=" => args[0].ge(&args[1]),
				"<=" => args[0].le(&args[1]),
				pred => {
					let domain: Vec<_> = args.iter().map(|_| Sort::int(ctx)).collect();
					let args: Vec<_> = args.iter().map(|int| Dynamic::from_ast(int)).collect();
					let f = FuncDecl::new(
						ctx,
						pred,
						&domain.iter().collect::<Vec<_>>(),
						&Sort::bool(ctx),
					);
					f.apply(&args.iter().collect::<Vec<_>>()).as_bool().unwrap()
				},
			}
		},
		_ => Bool::from_bool(ctx, true),
	}
}

fn trans_preds<'a>(ctx: &'a Context, preds: &[Predicate], env: &Env<Dynamic<'a>>, aggs: &mut HashMap<Agg, Dynamic<'a>>) -> Bool<'a> {
	let preds: Vec<_> = preds.iter().map(|pred| trans_pred(ctx, pred.clone(), env, aggs)).collect();
	Bool::and(ctx, &preds.iter().collect::<Vec<_>>())
}

fn trans_apps<'a>(ctx: &'a Context, apps: &[Application], env: &Env<Dynamic<'a>>) -> Int<'a> {
	if apps.is_empty() {
		return Int::from_i64(ctx, 1);
	}
	let apps: Vec<_> = apps
		.iter()
		.map(|app| {
			let domain: Vec<_> = app.args.iter().map(|_| Sort::int(ctx)).collect();
			let args: Vec<_> = app.args.iter().map(|v| env.get(*v)).collect();
			let f = FuncDecl::new(
				ctx,
				app.table.0.to_string(),
				&domain.iter().collect::<Vec<_>>(),
				&Sort::int(ctx),
			);
			f.apply(&args).as_int().unwrap()
		})
		.collect();
	Int::mul(ctx, &apps.iter().collect::<Vec<_>>())
}

fn trans_apps_squashed<'a>(
	ctx: &'a Context,
	apps: &[Application],
	env: &Env<Dynamic<'a>>,
) -> Bool<'a> {
	if apps.is_empty() {
		return Bool::from_bool(ctx, true);
	}
	let apps: Vec<_> = apps
		.iter()
		.map(|app| {
			let domain: Vec<_> = app.args.iter().map(|_| Sort::int(ctx)).collect();
			let args: Vec<_> = app.args.iter().map(|v| env.get(*v)).collect();
			let f = FuncDecl::new(
				ctx,
				app.table.0.to_string(),
				&domain.iter().collect::<Vec<_>>(),
				&Sort::bool(ctx),
			);
			f.apply(&args).as_bool().unwrap()
		})
		.collect();
	Bool::and(ctx, &apps.iter().collect::<Vec<_>>())
}

fn trans_squashed_term<'a>(
	ctx: &'a Context,
	term: &stable::Term,
	env: &Env<Dynamic<'a>>,
	aggs: &mut HashMap<Agg, Dynamic<'a>>,
) -> Bool<'a> {
	let vars = term.scopes.iter().map(|ty| Int::fresh_const(ctx, "v").into()).collect_vec();
	let env = &env.append(vars.clone());
	let preds = trans_preds(ctx, &term.preds, env, aggs);
	let apps = trans_apps_squashed(ctx, &term.apps, env);
	let not = term
		.not
		.as_ref()
		.map_or(Bool::from_bool(ctx, true), |n| trans_squashed(ctx, n, env, aggs).not());
	let body = Bool::and(ctx, &[&preds, &apps, &not]);
	exists_const(ctx, &vars.iter().collect_vec(), &[], &body).as_bool().unwrap()
}

fn trans_squashed<'a>(ctx: &'a Context, exp: &stable::UExpr, env: &Env<Dynamic<'a>>, aggs: &mut HashMap<Agg, Dynamic<'a>>) -> Bool<'a> {
	let terms =
		exp.0.iter().enumerate().map(|(i, term)| trans_squashed_term(ctx, term, env, aggs)).collect_vec();
	Bool::or(ctx, &terms.iter().collect_vec())
}

pub fn unify(rel1: &stable::Relation, rel2: &stable::Relation, env: &Env<Entry>) -> bool {
	match (rel1, rel2) {
		(Relation::Lam(tys1, uexpr1), Relation::Lam(tys2, uexpr2)) if tys1 == tys2 => {
			let env = &env.append_vars(tys1.clone());
			let cfg = Config::new();
			let ctx = Context::new(&cfg);
			let env = Env::new(env.entries.iter().map(|entry| match entry {
				Entry::Value(v, ty) => Int::fresh_const(&ctx, "v").into(),
				Entry::Table(v, sch) => Int::from_i64(&ctx, 0).into(),
			}));
			let solver = Solver::new(&ctx);
			unify_uexpr(&solver, uexpr1, uexpr2, &env, &env)
		},
		(Relation::Var(v1), Relation::Var(v2)) => v1 == v2,
		_ => false,
	}
}

fn unify_uexpr(
	solver: &Solver,
	exp1: &stable::UExpr,
	exp2: &stable::UExpr,
	env1: &Env<Dynamic>,
	env2: &Env<Dynamic>,
) -> bool {
	let terms1 = exp1.0.clone();
	let mut terms2 = exp2.0.clone();
	let paired = terms1.iter().all(|t1| {
		(0..terms2.len()).any(|i| {
			let t2 = &terms2[i];
			let unifies = unify_term(solver, t1, t2, env1, env2);
			if unifies {
				terms2.swap_remove(i);
			}
			unifies
		})
	});
	paired && terms2.is_empty()
}

fn perm_equiv<T: Ord + PartialEq + Clone>(v1: &[T], v2: &[T]) -> bool {
	if v1.len() == v2.len() {
		let mut v1 = v2.to_vec();
		let mut v2 = v2.to_vec();
		v1.sort();
		v2.sort();
		v1 == v2
	} else {
		false
	}
}

fn perms<T, V>(types: Vec<T>, vars: Vec<V>) -> impl Iterator<Item = Vec<V>>
where
	T: Ord + PartialEq + Clone,
	V: Clone,
{
	let sort_perm = permutation::sort(types.as_slice());
	let sorted_scopes = sort_perm.apply_slice(types.as_slice());
	let groups = sorted_scopes.iter().group_by(|a| *a);
	let group_lengths = if types.is_empty() {
		Either::Left(std::iter::once(0))
	} else {
		Either::Right(groups.into_iter().map(|(_, group)| group.count()))
	};
	let mut level = 0;
	let inv_sort_perm = sort_perm.inverse();
	group_lengths
		.map(|length| {
			let perms = (level..level + length).permutations(length);
			level += length;
			perms
		})
		.multi_cartesian_product()
		.map(move |perms| {
			let perm_vec = perms.into_iter().flatten().collect_vec();
			let permute = &inv_sort_perm * &permutation::Permutation::from_vec(perm_vec);
			permute.apply_slice(vars.as_slice())
		})
}

fn unify_term(
	solver: &Solver,
	t1: &stable::Term,
	t2: &stable::Term,
	env1: &Env<Dynamic>,
	env2: &Env<Dynamic>,
) -> bool {
	solver.push();
	defer!(solver.pop(1));
	if !perm_equiv(&t1.scopes, &t2.scopes) {
		return false;
	}
	let perm1 = permutation::sort(t1.scopes.as_slice());
	let ctx = solver.get_context();
	let vars1 = t1.scopes.iter().map(|ty| {
		use DataType::*;
		match ty {
			DataType::Boolean => Bool::fresh_const(ctx, "v").into(),
			Text | String => z3::ast::Int::fresh_const(ctx, "v").into(),
			_ => z3::ast::Int::fresh_const(ctx, "v").into(),
		}
	}).collect_vec();
	let vars = perm1.apply_slice(vars1.as_slice());
	let env1 = &env1.append(vars1);
	perms(t1.scopes.clone(), vars.clone()).take(10).any(|vars2| {
		log::info!("Permutation: {:?}", vars2);
		let aggs = &mut HashMap::new();
		let env2 = &env2.append(vars2);
		let preds1 = trans_preds(ctx, &t1.preds, env1, aggs);
		let preds2 = trans_preds(ctx, &t2.preds, env2, aggs);
		let apps1 = trans_apps(ctx, &t1.apps, env1);
		let apps2 = trans_apps(ctx, &t2.apps, env2);
		let apps_equiv = apps1._eq(&apps2);
		let squash1 = t1.squash.as_ref().map_or(Bool::from_bool(ctx, true), |sq| trans_squashed(ctx, sq, env1, aggs));
		let squash2 = t2.squash.as_ref().map_or(Bool::from_bool(ctx, true), |sq| trans_squashed(ctx, sq, env2, aggs));
		let not1 = t1.not.as_ref().map_or(Bool::from_bool(ctx, true), |n| trans_squashed(ctx, n, env1, aggs).not());
		let not2 = t2.not.as_ref().map_or(Bool::from_bool(ctx, true), |n| trans_squashed(ctx, n, env2, aggs).not());
		let logic1 = Bool::and(ctx, &[&preds1, &squash1, &not1]);
		let logic2 = Bool::and(ctx, &[&preds2, &squash2, &not2]);
		let equiv = Bool::and(ctx, &[&logic1.iff(&logic2), &apps_equiv]);
		log::info!("{}", equiv);
		solver.check_assumptions(&[equiv.not()]) == SatResult::Unsat
	})
}

struct SolverContext<'ctx> {
	solver: Solver<'ctx>,
	null_int: Nullable<'ctx, Int<'ctx>>,
	null_real: Nullable<'ctx, Real<'ctx>>,
}

impl<'ctx> SolverContext<'ctx> {
	pub fn new(solver: Solver<'ctx>) -> Self {
		let null_int = Nullable::<Int>::setup(&solver);
		let null_real = Nullable::<Real>::setup(&solver);
		SolverContext { solver, null_int, null_real }
	}
}

mod null;
