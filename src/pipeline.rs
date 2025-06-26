use std::rc::Rc;
use std::time::{Duration, Instant};
use std::collections::{HashMap, HashSet};

use imbl::vector;
use serde::{Deserialize, Serialize};
use z3::{Config, Context, Solver};

use crate::pipeline::normal::{Relation, Z3Env};
use crate::pipeline::shared::{Ctx, Eval, Schema};
use crate::pipeline::unify::{Unify, UnifyEnv};
use crate::pipeline::relation::{Relation as URelation, Expr, JoinKind, Constraint};
use crate::pipeline::enumerator::ConstraintEnumerator;
use crate::pipeline::filter::ConstraintFilter;

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
pub mod enumerator;
pub mod filter;

#[derive(Debug, Default, Clone)]
pub struct QueryInfo {
    /// 쿼리에서 사용된 릴레이션의 인덱스 Set
    pub relations: HashSet<usize>,
    /// 쿼리에서 사용된 속성(칼럼)의 Set (relation_index, column_index)
    pub attributes: HashSet<(usize, usize)>,
    /// 쿼리에서 사용된 미해석 술어(UDF)의 Set
    pub predicates: HashSet<String>,
    /// 쿼리에서 사용된 미해석 함수(UDF)의 Set (반환 타입: Non-Boolean)
    pub functions: HashSet<String>,
    /// 쿼리에서 사용된 집계 함수(Aggregation)의 Set
    pub aggregates: HashSet<String>,
}

impl QueryInfo {
    /// 두 쿼리 분석 결과를 병합하는 함수
    pub fn combine(mut self, other: Self) -> Self {
        self.relations.extend(other.relations);
        self.attributes.extend(other.attributes);
        self.predicates.extend(other.predicates);
        self.functions.extend(other.functions);
        self.aggregates.extend(other.aggregates);
        self
    }
}

/// 쿼리 쌍을 분석하여 사용된 요소 정보를 추출하는 최상위 함수
pub fn analyze_queries(queries: &(URelation, URelation), schemas: &[Schema]) -> QueryInfo {
    let (query1, query2) = queries;
    let mut info1 = QueryInfo::default();
    let mut info2 = QueryInfo::default();

    analyze_relation(query1, schemas, &mut info1, &mut Vec::new());
    analyze_relation(query2, schemas, &mut info2, &mut Vec::new());

    info1.combine(info2)
}

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

fn verify_with_constraints(
    schemas: &[Schema],
    query_pair: (URelation, URelation),
    constraints: &[Constraint],
    help: &(String, String)
) -> (bool, Stats) {
    let (mut rel1, mut rel2) = query_pair;
    let mut stats = Stats::default();
	let subst = vector![];
	let mut alias_map: HashMap<usize, usize> = HashMap::new(); // for RelEq
	let mut attrs_map: HashMap<Expr, Expr> = HashMap::new(); // for AttrsEq

	// 1단계: 제약 조건을 사용하여 쿼리 재작성 계획 수립 및 스키마 강화
    let mut temp_schemas = schemas.to_vec(); // 가변 스키마를 위해 복제
	for constraint in constraints {
		use crate::pipeline::relation::Expr::Col;
        use crate::pipeline::relation::Relation as RelationEnum;

        match constraint {
            Constraint::NotNull { r, a } => {
                if let Some(schema) = temp_schemas.get_mut(r.0) {
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
                if let Some(schema) = temp_schemas.get_mut(r.0) {
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
                if let Some(schema) = temp_schemas.get_mut(r1.0) {
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
            Constraint::RelEq { r1, r2 } => {
                if r1.0 < r2.0 {
                    alias_map.insert(r2.0, r1.0);
                } else {
                    alias_map.insert(r1.0, r2.0);
                }
            }
            Constraint::AttrsEq { a1, a2 } => {
               for (expr1, expr2) in a1.iter().zip(a2.iter()) {
                   attrs_map.insert(expr2.clone(), expr1.clone());
               }
            }
            _ => (),
        }
	}

    // 2단계: 수립된 계획에 따라 쿼리 재작성 실행
	rewrite_joins_for_refattrs(&mut rel1, constraints, &temp_schemas);
	rewrite_joins_for_refattrs(&mut rel2, constraints, &temp_schemas);

	// 수립된 계획에 따라 쿼리 재작성 실행
	if !alias_map.is_empty() {
		rewrite_scans(&mut rel1, &alias_map);
		rewrite_scans(&mut rel2, &alias_map);
	}

	if !attrs_map.is_empty() {
		rewrite_exprs(&mut rel1, &attrs_map);
		rewrite_exprs(&mut rel2, &attrs_map);
	}

    let env = relation::Env(&temp_schemas, &subst, 0);
	log::info!("Schemas:\n{:?}", temp_schemas);
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
		let formula = z3_env.eval_constraints(&temp_schemas, constraints);
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

pub fn unify(Input { schemas, queries, constraints, help }: Input) -> (bool, Stats) {
	if !constraints.is_empty() {
        return verify_with_constraints(&schemas, queries, &constraints, &help);
    }

    let (rel1, rel2) = queries;

    // 1단계: 쿼리 쌍 분석
	let (q1_info, q2_info) = {
        let mut info1 = QueryInfo::default();
        let mut info2 = QueryInfo::default();
        analyze_relation(&rel1, &schemas, &mut info1, &mut Vec::new());
        analyze_relation(&rel2, &schemas, &mut info2, &mut Vec::new());
        (info1, info2)
    };
    let combined_info = q1_info.clone().combine(q2_info.clone()); // 열거를 위해 결합
    log::info!("[Analysis] Detected Info: {:?}", combined_info);

    let filtered_constraints: Vec<Constraint> = if constraints.is_empty() {
        // 2단계: 분석 정보를 바탕으로 가능한 모든 제약 조건 생성
        let enumerated_constraints = ConstraintEnumerator::new().enumerate(&combined_info, &schemas);
        log::info!("[Enumeration] Generated {} constraint candidates.", enumerated_constraints.len());
        for (i, constraint) in enumerated_constraints.iter().enumerate() {
            log::info!("[Candidate {}] {:?}", i + 1, constraint);
        }

        // 3단계: "최소 조건 케이스"에 기반하여 불필요한 제약 조건 필터링
        let filter = ConstraintFilter::new(&q1_info, &q2_info, &rel1, &rel2, &schemas);
        let filtered = filter.filter(enumerated_constraints);
        log::info!("[Filtering] Filtered to {} meaningful constraints.", filtered.len());
        for (i, constraint) in filtered.iter().enumerate() {
            log::info!("[Filtered Candidate {}] {:?}", i + 1, constraint);
        }
        filtered
    } else {
        // 주어진 제약 조건을 그대로 사용
        log::info!("[Input Constraints] Using provided constraints directly.");
        for (i, constraint) in constraints.iter().enumerate() {
            log::info!("[Input Constraint {}] {:?}", i + 1, constraint);
        }
        constraints
    };
    
    // 4단계: 최소 제약 조건 탐색 (Minimal Constraint Search)
    let (initial_provable, initial_stats) = verify_with_constraints(&schemas, (rel1.clone(), rel2.clone()), &filtered_constraints, &help);

    if !initial_provable {
        log::info!("[SearchRelaxed] Not provable with all filtered constraints. Aborting search.");
        return (false, initial_stats);
    }

    log::info!("[SearchRelaxed] Provable with all constraints. Starting relaxation...");
    let mut minimal_constraints = filtered_constraints;

    let mut i = minimal_constraints.len();
    while i > 0 {
        i -= 1;
        let constraint_to_remove = minimal_constraints.remove(i);
        
        log::info!("[SearchRelaxed] Trying to remove: {:?}", constraint_to_remove);
        let (provable_after_removal, _) = verify_with_constraints(&schemas, (rel1.clone(), rel2.clone()), &minimal_constraints, &help);

        if !provable_after_removal {
             log::info!("[SearchRelaxed] FAILED: Constraint is essential. Keeping it.");
             minimal_constraints.insert(i, constraint_to_remove); // 다시 삽입
        } else {
            log::info!("[SearchRelaxed] SUCCESS: Constraint is redundant. Removing it.");
        }
    }

    log::info!("[SearchRelaxed] Found minimal constraint set ({} constraints):", minimal_constraints.len());
    for (i, constraint) in minimal_constraints.iter().enumerate() {
        log::info!("[Minimal Set {}] {:?}", i + 1, constraint);
    }

    (true, initial_stats)	
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

fn rewrite_joins_for_refattrs(rel: &mut URelation, constraints: &[Constraint], schemas: &[Schema]) {
    if let URelation::Join { left, right, kind, condition } = rel {
        // 재귀적으로 하위 조인부터 처리
        rewrite_joins_for_refattrs(left, &constraints, &schemas);
        rewrite_joins_for_refattrs(right, &constraints, &schemas);

        // 현재 조인이 LEFT JOIN인 경우에만 INNER JOIN으로의 변환을 시도
        if *kind == JoinKind::Left {
			let left_width = left.scope(schemas).len();
            for constraint in constraints {
                if let Constraint::RefAttrs { r1, a1, r2, a2 } = constraint {
                    // 이 조인이 해당 RefAttrs 제약조건과 일치하는지 확인
                    if match_ref_attrs(left, right, condition, *r1, a1, *r2, a2, left_width) {
                        *kind = JoinKind::Inner;
                        log::info!("Rewrote LEFT JOIN to INNER JOIN based on RefAttrs");
                        break; // 변환이 적용되었으므로 더 이상 확인할 필요 없음
                    }
                }
            }
        }
    } else {
        // 다른 타입의 릴레이션에 대해서도 재귀적으로 순회
        match rel {
            URelation::Filter { source, .. } => rewrite_joins_for_refattrs(source, constraints, schemas),
            URelation::Project { source, .. } => rewrite_joins_for_refattrs(source, constraints, schemas),
            URelation::Union(rels) | URelation::Intersect(rels) => {
                for r in rels { rewrite_joins_for_refattrs(r, constraints, schemas); }
            },
            URelation::Except(l, r) => {
                rewrite_joins_for_refattrs(l, constraints, schemas);
                rewrite_joins_for_refattrs(r, constraints, schemas);
            },
            URelation::Distinct(s) | URelation::Sort { source: s, .. } | URelation::Aggregate { source: s, .. } | URelation::Group { source: s, .. } => {
                rewrite_joins_for_refattrs(s, constraints, schemas);
            },
            _ => {}
        }
    }
}

fn match_ref_attrs(
    left: &URelation,
    right: &URelation,
    condition: &Expr,
    r1: crate::pipeline::shared::VL,
    a1: &[Expr],
    r2: crate::pipeline::shared::VL,
    a2: &[Expr],
    left_width: usize,
) -> bool {
    let rels_match = matches!((left, right), (URelation::Scan(vl1), URelation::Scan(vl2)) if vl1.0 == r1.0 && vl2.0 == r2.0);
    if !rels_match { return false; }

    if let Expr::Op { op, args, .. } = condition {
        if op == "=" && args.len() == 2 {
            if let (Expr::Col { column: c1, .. }, Expr::Col { column: c2, .. }) = (&args[0], &args[1]) {
                let const_c1 = a1.get(0).and_then(|e| if let Expr::Col{column, ..} = e {Some(column.0)} else {None}).unwrap_or(usize::MAX);
                let const_c2 = a2.get(0).and_then(|e| if let Expr::Col{column, ..} = e {Some(column.0)} else {None}).unwrap_or(usize::MAX);

                // Case 1: cond(c1, c2) == constr(a1, a2) -> c1은 left, c2는 right
                let case1 = c1.0 == const_c1 && c2.0 == left_width + const_c2;
                // Case 2: cond(c2, c1) == constr(a1, a2) -> c2는 left, c1는 right
                let case2 = c2.0 == const_c1 && c1.0 == left_width + const_c2;

                return case1 || case2;
            }
        }
    }
    false
}

// [수정] AttrsEq를 위한 재귀적 표현식 재작성 함수
fn rewrite_exprs(rel: &mut URelation, attrs_map: &HashMap<Expr, Expr>) {
    fn rewrite_single_expr(expr: &mut Expr, attrs_map: &HashMap<Expr, Expr>) {
        if let Some(target_expr) = attrs_map.get(expr) {
            *expr = target_expr.clone();
            return;
        }
        match expr {
            Expr::Op { args, rel, .. } => {
                for arg in args {
                    rewrite_single_expr(arg, attrs_map);
                }
                if let Some(sub_rel) = rel {
                    rewrite_exprs(sub_rel, attrs_map);
                }
            }
            Expr::Col { .. } => {}
        }
    }

    match rel {
        URelation::Filter { condition, source } => {
            rewrite_single_expr(condition, attrs_map);
            rewrite_exprs(source, attrs_map);
        }
        URelation::Project { columns, source } => {
            for col in columns {
                rewrite_single_expr(col, attrs_map);
            }
            rewrite_exprs(source, attrs_map);
        }
        URelation::Join { left, right, condition, .. } => {
            rewrite_exprs(left, attrs_map);
            rewrite_exprs(right, attrs_map);
            rewrite_single_expr(condition, attrs_map);
        }
        URelation::Correlate { left, right, .. } => {
            rewrite_exprs(left, attrs_map);
            rewrite_exprs(right, attrs_map);
        }
        URelation::Union(rels) | URelation::Intersect(rels) => {
            for r in rels {
                rewrite_exprs(r, attrs_map);
            }
        }
        URelation::Except(left, right) => {
            rewrite_exprs(left, attrs_map);
            rewrite_exprs(right, attrs_map);
        }
        URelation::Distinct(source) => rewrite_exprs(source, attrs_map),
        URelation::Sort { source, .. } => rewrite_exprs(source, attrs_map),
        URelation::Aggregate { columns, source } => {
            for agg_call in columns {
                for arg in &mut agg_call.args {
                    rewrite_single_expr(arg, attrs_map);
                }
            }
            rewrite_exprs(source, attrs_map);
        }
        URelation::Group { keys, columns, source } => {
            for key in keys {
                rewrite_single_expr(key, attrs_map);
            }
            for agg_call in columns {
                for arg in &mut agg_call.args {
                    rewrite_single_expr(arg, attrs_map);
                }
            }
            rewrite_exprs(source, attrs_map);
        }
        _ => (),
    }
}

/// Relation 트리를 재귀적으로 순회하며 정보를 분석하는 함수.
/// `current_scope`는 현재 컨텍스트에서 접근 가능한 (릴레이션 인덱스, 칼럼 수)의 목록입니다.
fn analyze_relation(rel: &URelation, schemas: &[Schema], info: &mut QueryInfo, current_scope: &mut Vec<(usize, usize)>) {
    match rel {
        URelation::Scan(vl) => {
            info.relations.insert(vl.0);
            // 현재 스캔하는 릴레이션의 정보를 스코프에 추가
            current_scope.push((vl.0, schemas[vl.0].types.len()));
        }
        URelation::Filter { condition, source } => {
            analyze_relation(source, schemas, info, current_scope);
            analyze_expr(condition, schemas, info, current_scope);
        }
        URelation::Project { columns, source } => {
            analyze_relation(source, schemas, info, current_scope);
            for col in columns {
                analyze_expr(col, schemas, info, current_scope);
            }
        }
        URelation::Join { left, right, condition, .. } => {
            let mut left_scope = Vec::new();
            analyze_relation(left, schemas, info, &mut left_scope);

            let mut right_scope = Vec::new();
            analyze_relation(right, schemas, info, &mut right_scope);
            
            // Join된 새로운 스코프를 생성하여 상위로 전달
            current_scope.extend(left_scope.clone());
            current_scope.extend(right_scope);
            
            // 조인 조건 분석 시, 결합된 스코프를 전달
            analyze_expr(condition, schemas, info, current_scope);
        }
        URelation::Union(rels) | URelation::Intersect(rels) => {
            for r in rels {
                analyze_relation(r, schemas, info, &mut Vec::new()); // Union/Intersect는 scope를 공유하지 않음
            }
        }
        URelation::Except(left, right) => {
            analyze_relation(left, schemas, info, &mut Vec::new());
            analyze_relation(right, schemas, info, &mut Vec::new());
        }
        URelation::Distinct(source) | URelation::Sort { source, .. } => {
            analyze_relation(source, schemas, info, current_scope);
        }
        URelation::Aggregate { columns, source } => {
            analyze_relation(source, schemas, info, current_scope);
            for agg_call in columns {
                info.aggregates.insert(agg_call.op.clone());
                for arg in &agg_call.args {
                    analyze_expr(arg, schemas, info, current_scope);
                }
            }
        }
        URelation::Group { keys, columns, source } => {
            analyze_relation(source, schemas, info, current_scope);
            for key in keys {
                analyze_expr(key, schemas, info, current_scope);
            }
            for agg_call in columns {
                info.aggregates.insert(agg_call.op.clone());
                for arg in &agg_call.args {
                    analyze_expr(arg, schemas, info, current_scope);
                }
            }
        }
        _ => (),
    }
}

/// Expr 트리를 재귀적으로 순회하며 정보를 분석하는 함수
fn analyze_expr(expr: &Expr, schemas: &[Schema], info: &mut QueryInfo, current_scope: &[(usize, usize)]) {
    match expr {
        Expr::Col { column, .. } => {
            let mut offset = 0;
            for &(rel_idx, arity) in current_scope {
                if column.0 >= offset && column.0 < offset + arity {
                    // 원래 칼럼 인덱스(0-based)로 변환하여 (릴레이션 인덱스, 칼럼 인덱스) 쌍을 추가
                    info.attributes.insert((rel_idx, column.0 - offset));
                    return;
                }
                offset += arity;
            }
        }
        Expr::Op { op, args, ty, rel, .. } => {
            // 숫자 리터럴인지 확인하는 로직 추가
            let is_numeric_literal = op.parse::<i64>().is_ok() || op.parse::<f64>().is_ok();
            let is_standard_op = relation::num_op(op) || relation::num_cmp(op) || matches!(op.as_str(), "IN" | "AND" | "OR" | "NOT" | "IS NULL" | "IS NOT NULL");
            
            if !is_numeric_literal && !is_standard_op {
                // 반환 타입에 따라 술어와 함수를 구분하여 저장
                if *ty == crate::pipeline::shared::DataType::Boolean {
                    info.predicates.insert(op.clone());
                } else {
                    info.functions.insert(op.clone());
                }
            }

            for arg in args {
                analyze_expr(arg, schemas, info, current_scope);
            }
            if let Some(sub_rel) = rel {
                analyze_relation(sub_rel, schemas, info, &mut Vec::new());
            }
        }
    }
}
