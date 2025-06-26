use std::collections::HashSet;
use crate::pipeline::relation::{Constraint, Expr, JoinKind, Relation as URelation};
use crate::pipeline::shared::{Schema, VL, DataType};
use crate::pipeline::QueryInfo;

/// 제약 조건 필터링을 수행하는 구조체
pub struct ConstraintFilter<'a> {
    q1_info: &'a QueryInfo,
    q2_info: &'a QueryInfo,
    q1: &'a URelation,
    q2: &'a URelation,
    schemas: &'a [Schema],
}

impl<'a> ConstraintFilter<'a> {
    pub fn new(q1_info: &'a QueryInfo, q2_info: &'a QueryInfo, q1: &'a URelation, q2: &'a URelation, schemas: &'a [Schema]) -> Self {
        Self { q1_info, q2_info, q1, q2, schemas }
    }

    /// 주어진 제약 조건 목록에 대해 모든 필터링 규칙을 적용합니다.
    pub fn filter(&self, constraints: Vec<Constraint>) -> Vec<Constraint> {
        constraints.into_iter().filter(|c| self.is_meaningful(c)).collect()
    }

    /// 특정 제약 조건이 "최소 조건 케이스"를 만족하는지 확인하는 메인 분기 함수
    fn is_meaningful(&self, constraint: &Constraint) -> bool {
        match constraint {
            Constraint::RelEq { r1, r2 } => self.filter_rel_eq(*r1, *r2),
            Constraint::AttrsEq { a1, a2 } => self.filter_attrs_eq(a1, a2),
            Constraint::PredEq { p1, p2 } => self.filter_pred_eq(p1, p2),
            Constraint::SubAttr { a1, a2 } => self.filter_sub_attr(a1, a2),
            Constraint::RefAttrs { r1, a1, r2, a2 } => self.filter_ref_attrs(*r1, a1, *r2, a2),
            Constraint::Unique { r, a } => self.filter_uniqueness(*r, a),
            Constraint::NotNull { r, a } => self.filter_not_null(*r, a),
        }
    }

    // --- 각 제약 조건별 필터링 규칙 구현 ---

    fn filter_rel_eq(&self, r1: VL, r2: VL) -> bool {
        // 한 쿼리는 r1을, 다른 쿼리는 r2를 사용하는 비대칭적 구조인지 확인
        (self.q1_info.relations.contains(&r1.0) && self.q2_info.relations.contains(&r2.0) && !self.q1_info.relations.contains(&r2.0)) ||
        (self.q1_info.relations.contains(&r2.0) && self.q2_info.relations.contains(&r1.0) && !self.q1_info.relations.contains(&r1.0))
    }

    fn filter_attrs_eq(&self, a1: &[Expr], a2: &[Expr]) -> bool {
        // 쿼리 내에서 두 속성이 비대칭적으로 사용되었는지 확인
        let expr1 = &a1[0];
        let expr2 = &a2[0];
        (find_expr_in_relation(self.q1, expr1) && find_expr_in_relation(self.q2, expr2) && !find_expr_in_relation(self.q1, expr2)) ||
        (find_expr_in_relation(self.q1, expr2) && find_expr_in_relation(self.q2, expr1) && !find_expr_in_relation(self.q1, expr1))
    }

    fn filter_pred_eq(&self, p1: &Box<Expr>, p2: &Box<Expr>) -> bool {
        // 두 술어가 각 쿼리에 나뉘어 등장하는지 확인
        let op1 = if let Expr::Op { op, .. } = &**p1 { op.clone() } else { return false; };
        let op2 = if let Expr::Op { op, .. } = &**p2 { op.clone() } else { return false; };
        (self.q1_info.predicates.contains(&op1) && self.q2_info.predicates.contains(&op2)) ||
        (self.q1_info.predicates.contains(&op2) && self.q2_info.predicates.contains(&op1))
    }
    
    fn filter_sub_attr(&self, a1: &[Expr], a2: &[Expr]) -> bool {
        // f(g(x))와 f(x) 형태가 비대칭적으로 존재하는지 확인
        let f_of_g = if let Expr::Op { op: f_op, .. } = &a1[0] {
            if let Expr::Op { .. } = &a2[0] {
                Some(Expr::Op { op: f_op.clone(), args: vec![a2[0].clone()], ty: a1[0].ty(), rel: None })
            } else { None }
        } else { None };

        if let Some(f_of_g_expr) = f_of_g {
            return (find_expr_in_relation(self.q1, &f_of_g_expr) && find_expr_in_relation(self.q2, &a1[0])) ||
                   (find_expr_in_relation(self.q2, &f_of_g_expr) && find_expr_in_relation(self.q1, &a1[0]));
        }
        false
    }
    
    fn filter_ref_attrs(&self, r1: VL, a1: &[Expr], r2: VL, a2: &[Expr]) -> bool {
        // Case 1: LEFT JOIN vs INNER JOIN 비대칭성
        let q1_has_left_join = has_specific_join(self.q1, &JoinKind::Left, r1, a1, r2, a2, self.schemas);
        if q1_has_left_join && !has_specific_join(self.q2, &JoinKind::Left, r1, a1, r2, a2, self.schemas) { return true; }
        if !q1_has_left_join && has_specific_join(self.q2, &JoinKind::Left, r1, a1, r2, a2, self.schemas) { return true; }

        // Case 2: IN 서브쿼리 유무 비대칭성
        let q1_has_in = has_in_subquery(self.q1, a1, r2, a2);
        let q2_has_in = has_in_subquery(self.q2, a1, r2, a2);
        if q1_has_in != q2_has_in { return true; }
        
        // Case 3: EXISTS 서브쿼리 유무 비대칭성
        let q1_has_exists = has_exists_subquery(self.q1, a1, r2, a2);
        let q2_has_exists = has_exists_subquery(self.q2, a1, r2, a2);
        if q1_has_exists != q2_has_exists { return true; }

        false
    }

    fn filter_uniqueness(&self, r: VL, _a: &[Expr]) -> bool {
        let q1_has_self_join = has_self_join(self.q1, r);
        let q2_has_self_join = has_self_join(self.q2, r);
        let q1_has_distinct = has_distinct(self.q1);
        let q2_has_distinct = has_distinct(self.q2);

        (q1_has_self_join != q2_has_self_join) || (q1_has_distinct != q2_has_distinct)
    }

    fn filter_not_null(&self, _r: VL, a: &[Expr]) -> bool {
        let attr = &a[0];
        let q1_has_not_null = has_is_not_null_filter(self.q1, attr);
        let q2_has_not_null = has_is_not_null_filter(self.q2, attr);
        q1_has_not_null != q2_has_not_null
    }
}

// --- 필터링 규칙을 위한 재귀적 헬퍼 함수들 ---

fn find_expr_in_relation(rel: &URelation, target_expr: &Expr) -> bool {
    let mut found = false;
    find_expr_recursive(rel, target_expr, &mut found);
    found
}

fn find_expr_recursive(current_rel: &URelation, target: &Expr, found: &mut bool) {
    if *found { return; }
    match current_rel {
        URelation::Filter { condition, source } => {
            find_in_expr(condition, target, found);
            find_expr_recursive(source, target, found);
        }
        URelation::Project { columns, source } => {
            for col in columns { find_in_expr(col, target, found); }
            find_expr_recursive(source, target, found);
        }
        URelation::Join { left, right, condition, .. } => {
            find_in_expr(condition, target, found);
            find_expr_recursive(left, target, found);
            find_expr_recursive(right, target, found);
        }
        URelation::Correlate { left, right, .. } => {
            find_expr_recursive(left, target, found);
            find_expr_recursive(right, target, found);
        }
        URelation::Union(rels) | URelation::Intersect(rels) => {
            for r in rels { find_expr_recursive(r, target, found); }
        }
        URelation::Except(left, right) => {
            find_expr_recursive(left, target, found);
            find_expr_recursive(right, target, found);
        }
        URelation::Distinct(source) | URelation::Sort { source, .. } => {
            find_expr_recursive(source, target, found);
        }
        URelation::Aggregate { columns, source } => {
            for agg in columns { for arg in &agg.args { find_in_expr(arg, target, found); } }
            find_expr_recursive(source, target, found);
        }
        URelation::Group { keys, columns, source } => {
            for key in keys { find_in_expr(key, target, found); }
            for agg in columns { for arg in &agg.args { find_in_expr(arg, target, found); } }
            find_expr_recursive(source, target, found);
        }
        _ => (), 
    }
}

fn find_in_expr(expr: &Expr, target: &Expr, found: &mut bool) {
    if *found { return; }
    if expr == target {
        *found = true;
        return;
    }
    if let Expr::Op { args, rel, .. } = expr {
        for arg in args {
            find_in_expr(arg, target, found);
        }
        if let Some(sub_rel) = rel {
            find_expr_recursive(sub_rel, target, found);
        }
    }
}

fn has_specific_join(rel: &URelation, kind: &JoinKind, r1: VL, a1: &[Expr], r2: VL, a2: &[Expr], schemas: &[Schema]) -> bool {
    let mut found = false;
    fn find_recursive(current_rel: &URelation, kind: &JoinKind, r1: VL, a1: &[Expr], r2: VL, a2: &[Expr], schemas: &[Schema], found: &mut bool) {
        if *found { return; }
        if let URelation::Join { left, right, kind: join_kind, condition } = current_rel {
            let left_width = left.scope(schemas).len();
            if kind == join_kind && crate::pipeline::match_ref_attrs(left, right, condition, r1, a1, r2, a2, left_width) {
                *found = true;
                return;
            }
        }
        match current_rel {
            URelation::Filter { source, .. } | URelation::Project { source, .. } | URelation::Distinct(source) |
            URelation::Sort { source, .. } | URelation::Aggregate { source, .. } | URelation::Group { source, .. } => {
                find_recursive(source, kind, r1, a1, r2, a2, schemas, found);
            }
            URelation::Join { left, right, .. } | URelation::Correlate { left, right, .. } | URelation::Except(left, right) => {
                find_recursive(left, kind, r1, a1, r2, a2, schemas, found);
                find_recursive(right, kind, r1, a1, r2, a2, schemas, found);
            }
            URelation::Union(rels) | URelation::Intersect(rels) => {
                for r in rels { find_recursive(r, kind, r1, a1, r2, a2, schemas, found); }
            }
            _ => {}
        }
    }
    find_recursive(rel, kind, r1, a1, r2, a2, schemas, &mut found);
    found
}

fn contains_scan(rel: &URelation, r_idx: usize) -> bool {
    let mut inner_found = false;
    fn find_recursive_scan(current_rel: &URelation, r_idx: usize, found: &mut bool) {
        if *found { return; }
        if let URelation::Scan(vl) = current_rel {
            if vl.0 == r_idx { *found = true; return; }
        }
        match current_rel {
             URelation::Filter { source, .. } | URelation::Project { source, .. } | URelation::Distinct(source) |
             URelation::Sort { source, .. } | URelation::Aggregate { source, .. } | URelation::Group { source, .. } => find_recursive_scan(source, r_idx, found),
             URelation::Join { left, right, .. } | URelation::Correlate { left, right, .. } | URelation::Except(left, right) => { find_recursive_scan(left, r_idx, found); find_recursive_scan(right, r_idx, found); }
             URelation::Union(rels) | URelation::Intersect(rels) => { for r in rels { find_recursive_scan(r, r_idx, found); } }
             _ => {}
        }
    }
    find_recursive_scan(rel, r_idx, &mut inner_found);
    inner_found
}

fn has_self_join(rel: &URelation, r: VL) -> bool {
    let mut found = false;
    fn find_recursive(current_rel: &URelation, r_idx: usize, found: &mut bool) {
        if *found { return; }
        if let URelation::Join { left, right, .. } = current_rel {
            if contains_scan(left, r_idx) && contains_scan(right, r_idx) {
                *found = true;
                return;
            }
        }
        match current_rel {
            URelation::Filter { source, .. } | URelation::Project { source, .. } | URelation::Distinct(source) |
            URelation::Sort { source, .. } | URelation::Aggregate { source, .. } | URelation::Group { source, .. } => find_recursive(source, r_idx, found),
            URelation::Join { left, right, .. } | URelation::Correlate { left, right, .. } | URelation::Except(left, right) => { find_recursive(left, r_idx, found); find_recursive(right, r_idx, found); }
            URelation::Union(rels) | URelation::Intersect(rels) => { for r in rels { find_recursive(r, r_idx, found); } }
            _ => {}
        }
    }
    find_recursive(rel, r.0, &mut found);
    found
}

fn has_distinct(rel: &URelation) -> bool {
    let mut found = false;
    fn find_recursive(current_rel: &URelation, found: &mut bool) {
        if *found { return; }
        if matches!(current_rel, URelation::Distinct(_)) {
            *found = true;
            return;
        }
        match current_rel {
            URelation::Filter { source, .. } | URelation::Project { source, .. } | URelation::Sort { source, .. } |
            URelation::Aggregate { source, .. } | URelation::Group { source, .. } => find_recursive(source, found),
            URelation::Join { left, right, .. } | URelation::Correlate { left, right, .. } | URelation::Except(left, right) => { find_recursive(left, found); find_recursive(right, found); }
            URelation::Union(rels) | URelation::Intersect(rels) => { for r in rels { find_recursive(r, found); } }
            _ => {}
        }
    }
    find_recursive(rel, &mut found);
    found
}

fn has_is_not_null_filter(rel: &URelation, attr: &Expr) -> bool {
    let target_expr = Expr::Op { op: "IS NOT NULL".to_string(), args: vec![attr.clone()], ty: DataType::Boolean, rel: None };
    find_expr_in_relation(rel, &target_expr)
}

fn has_in_subquery(rel: &URelation, a1: &[Expr], r2: VL, a2: &[Expr]) -> bool {
    // a1은 외부 쿼리의 속성이므로, rel 트리 전체에서 a1이 사용되는지 확인
    if !find_expr_in_relation(rel, &a1[0]) {
        return false;
    }
    // IN 연산자의 서브쿼리 부분이 제약조건의 r2, a2와 일치하는지 확인
    let target_subquery = Expr::Op {
        op: "IN".to_string(),
        args: vec![a1[0].clone()],
        ty: DataType::Boolean,
        rel: Some(Box::new(URelation::Project {
            columns: vec![a2[0].clone()],
            source: Box::new(URelation::Scan(r2)),
        })),
    };
    find_expr_in_relation(rel, &target_subquery)
}

fn has_exists_subquery(rel: &URelation, a1: &[Expr], r2: VL, a2: &[Expr]) -> bool {
    let mut found = false;
    // EXISTS (SELECT * FROM r2 WHERE r1.a1 = r2.a2) 패턴을 찾음
    let join_condition = Expr::Op {
        op: "=".to_string(),
        args: vec![a1[0].clone(), a2[0].clone()],
        ty: DataType::Boolean,
        rel: None,
    };

    fn find_recursive(current_rel: &URelation, r2_idx: usize, join_cond: &Expr, found: &mut bool) {
        if *found { return; }
        if let URelation::Filter { condition, .. } = current_rel {
            if let Expr::Op { op, rel: Some(subquery), .. } = condition {
                if op == "EXISTS" {
                    if let URelation::Filter { condition: sub_cond, source } = &**subquery {
                        if **source == URelation::Scan(VL(r2_idx)) && sub_cond == join_cond {
                            *found = true;
                            return;
                        }
                    }
                }
            }
        }
        // Recurse into children
        match current_rel {
            URelation::Filter { source, .. } | URelation::Project { source, .. } | URelation::Distinct(source) |
            URelation::Sort { source, .. } | URelation::Aggregate { source, .. } | URelation::Group { source, .. } => {
                find_recursive(source, r2_idx, join_cond, found);
            }
            URelation::Join { left, right, .. } | URelation::Correlate { left, right, .. } | URelation::Except(left, right) => {
                find_recursive(left, r2_idx, join_cond, found);
                find_recursive(right, r2_idx, join_cond, found); 
            }
            URelation::Union(rels) | URelation::Intersect(rels) => {
                for r in rels { find_recursive(r, r2_idx, join_cond, found); }
            }
            _ => (),
        }
    }
    find_recursive(rel, r2.0, &join_condition, &mut found);
    found
}
