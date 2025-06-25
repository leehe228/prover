use std::rc::Rc;
use std::time::{Duration, Instant};
use std::collections::HashMap;

use imbl::vector;
use serde::{Deserialize, Serialize};
use z3::{Config, Context, Solver};

use crate::pipeline::normal::{Relation, Z3Env};
use crate::pipeline::shared::{Ctx, Eval, Schema};
use crate::pipeline::unify::{Unify, UnifyEnv};
use crate::pipeline::relation::{Relation as URelation, Expr};

pub mod normal;
mod null;
pub mod partial;
pub mod relation;
pub mod shared;
pub mod stable;
pub mod syntax;
#[cfg(test)]
mod tests;
pub mod unify;

#[derive(Serialize, Deserialize)]
pub struct Input {
	schemas: Vec<Schema>,
	pub queries: (relation::Relation, relation::Relation),
	#[serde(default)]
	pub constraints: Vec<relation::Constraint>,
	#[serde(default)]
	help: (String, String),
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Stats {
	pub provable: bool,
	pub panicked: bool,
	pub complete_fragment: bool,
	pub equiv_class_duration: Duration,
	pub equiv_class_timed_out: bool,
	pub smt_duration: Duration,
	pub smt_timed_out: bool,
	pub nontrivial_perms: bool,
	pub translate_duration: Duration,
	pub normal_duration: Duration,
	pub stable_duration: Duration,
	pub unify_duration: Duration,
	pub total_duration: Duration,
}

pub fn unify(Input { mut schemas, queries: (mut rel1, mut rel2), constraints, help }: Input) -> (bool, Stats) {
	let mut stats = Stats::default();
	let subst = vector![];
	let mut alias_map: HashMap<usize, usize> = HashMap::new();

	for constraint in &constraints {
		use crate::pipeline::relation::{Constraint, Expr, Relation as RelationEnum};
		use crate::pipeline::relation::Expr::Col;

		match constraint {
			Constraint::NotNull { r, a } => {
				if let Some(schema) = schemas.get_mut(r.0) {
					for expr in a {
						if let Col { column, .. } = expr {
							if let Some(nullable) = schema.nullabilities.get_mut(column.0) {
								*nullable = false;
							}
						}
					}
				}
			}
			Constraint::Unique { r, a } => {
				if let Some(schema) = schemas.get_mut(r.0) {
					let key_set: std::collections::HashSet<usize> = a.iter().filter_map(|expr| {
						if let Col { column, .. } = expr { Some(column.0) } else { None }
					}).collect();
					if !key_set.is_empty() {
						if !schema.primary.contains(&key_set) {
							schema.primary.push(key_set);
						}
					}
				}
			}
			Constraint::RefAttrs { r1, a1, r2, a2 } => {
				if let Some(schema) = schemas.get_mut(r1.0) {
					// a1 IN (SELECT a2 FROM r2) 형태의 guaranteed predicate를 생성
					let subquery = RelationEnum::Project {
						columns: a2.clone(),
						source: Box::new(RelationEnum::Scan(*r2)),
					};
					let in_expr = Expr::Op {
						op: "IN".to_string(),
						args: a1.clone(),
						ty: crate::pipeline::shared::DataType::Boolean,
						rel: Some(Box::new(subquery)),
					};
					schema.guaranteed.push(in_expr);
				}
			}
			// AttrsEq, PredEq, SubAttrs는 SMT Axiom으로 처리됨 (사전 구조 변경 필요 X)
			Constraint::RelEq { r1, r2 } => {
				// r2를 보면 r1으로 취급하도록 alias map에 기록 (큰 인덱스 -> 작은 인덱스)
				if r1.0 < r2.0 {
					alias_map.insert(r2.0, r1.0);
				} else {
					alias_map.insert(r1.0, r2.0);
				}
			}
			_ => (),
		}
	}

	// RelEq 쿼리 재작성
	if !alias_map.is_empty() {
		rewrite_scans(&mut rel1, &alias_map);
		rewrite_scans(&mut rel2, &alias_map);
	}

	let env = relation::Env(&schemas, &subst, 0);
	log::info!("Schemas:\n{:?}", schemas);
	log::info!("Input:\n{}\n{}", help.0, help.1);
	stats.complete_fragment = rel1.complete() && rel2.complete();
	if rel1 == rel2 {
		println!("Trivially true!");
		return (true, stats);
	}
	let syn_start = Instant::now();
	let rel1 = env.eval(rel1);
	let rel2 = env.eval(rel2);
	stats.translate_duration = syn_start.elapsed();
	log::info!("Syntax left:\n{}", rel1);
	log::info!("Syntax right:\n{}", rel2);
	if rel1 == rel2 {
		return (true, stats);
	}
	let nom_env = &vector![];
	let eval_nom = |rel: syntax::Relation| -> normal::Relation {
		let rel = (&partial::Env::default()).eval(rel);
		nom_env.eval(rel)
	};
	let norm_start = Instant::now();
	let rel1 = eval_nom(rel1);
	let rel2 = eval_nom(rel2);
	stats.normal_duration = norm_start.elapsed();
	log::info!("Normal left:\n{}", rel1);
	log::info!("Normal right:\n{}", rel2);
	if rel1 == rel2 {
		return (true, stats);
	}
	let config = Config::new();
	let z3_ctx = &Context::new(&config);
	let ctx = Rc::new(Ctx::new_with_stats(Solver::new(z3_ctx), stats));
	let z3_env = Z3Env::empty(ctx.clone());

	if !constraints.is_empty() {
		let formula = z3_env.eval_constraints(&schemas, &constraints);
		log::info!("Global Constraints Formula:\n{}", formula);
		ctx.constraints_formula.replace(Some(formula));
	}

	let eval_stb = |nom: normal::Relation| -> normal::Relation {
		let env = &stable::Env(vector![], z3_env.clone());
		let stb = env.eval(nom);
		nom_env.eval(stb)
	};
	let stb_start = Instant::now();

	log::info!("\n--- Left Query ---");
	log::info!("# Before Stabilization (Normal Form):\n{}", rel1);
	let rel1 = eval_stb(rel1);
	log::info!("# After Stabilization (Stable Form):\n{}", rel1);

	log::info!("\n--- Right Query ---");
	log::info!("# Before Stabilization (Normal Form):\n{}", rel2);
	let rel2 = eval_stb(rel2);
	log::info!("# After Stabilization (Stable Form):\n{}", rel2);

	ctx.stats.borrow_mut().stable_duration = stb_start.elapsed();
	if rel1 == rel2 {
		return (true, ctx.stats.borrow().clone());
	}
	let env = UnifyEnv(ctx.clone(), vector![], vector![]);
	let unify_start = Instant::now();
	let res = env.unify(&rel1, &rel2);
	ctx.stats.borrow_mut().unify_duration = unify_start.elapsed();
	let stats = ctx.stats.borrow().clone();
	(res, stats)
}

fn rewrite_scans(rel: &mut URelation, alias_map: &HashMap<usize, usize>) {
    match rel {
        URelation::Scan(vl) => {
            if let Some(&target_vl) = alias_map.get(&vl.0) {
                vl.0 = target_vl;
            }
        }
        URelation::Filter { source, condition } => {
			rewrite_expr_scans(condition, alias_map);
			rewrite_scans(source, alias_map);
		}
		URelation::Project { columns, source } => {
			for col in columns {
				rewrite_expr_scans(col, alias_map);
			}
			rewrite_scans(source, alias_map);
		}
        URelation::Join { left, right, condition, .. } => {
            rewrite_scans(left, alias_map);
            rewrite_scans(right, alias_map);
            rewrite_expr_scans(condition, alias_map);
        }
        URelation::Correlate { left, right, .. } => {
             rewrite_scans(left, alias_map);
             rewrite_scans(right, alias_map);
        }
        URelation::Union(rels) | URelation::Intersect(rels) => {
            for r in rels {
                rewrite_scans(r, alias_map);
            }
        }
        URelation::Except(left, right) => {
            rewrite_scans(left, alias_map);
            rewrite_scans(right, alias_map);
        }
        URelation::Distinct(source) | URelation::Sort { source, .. } | URelation::Aggregate { source, .. } | URelation::Group { source, .. } => {
            rewrite_scans(source, alias_map)
        }
        URelation::Singleton | URelation::Values { .. } => (),
    }
}

fn rewrite_expr_scans(expr: &mut Expr, alias_map: &HashMap<usize, usize>) {
    if let Expr::Op { args, rel: Some(sub_rel), .. } = expr {
        for arg in args {
            rewrite_expr_scans(arg, alias_map);
        }
        rewrite_scans(sub_rel, alias_map);
    }
}
