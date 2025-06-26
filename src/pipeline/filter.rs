use std::collections::HashSet;
use crate::pipeline::relation::{Constraint, Expr, JoinKind, Relation as URelation};
use crate::pipeline::shared::VL;
use crate::pipeline::QueryInfo;

/// 제약 조건 필터링을 수행하는 구조체
pub struct ConstraintFilter<'a> {
    q1_info: &'a QueryInfo,
    q2_info: &'a QueryInfo,
    q1: &'a URelation,
    q2: &'a URelation,
}

impl<'a> ConstraintFilter<'a> {
    pub fn new(q1_info: &'a QueryInfo, q2_info: &'a QueryInfo, q1: &'a URelation, q2: &'a URelation) -> Self {
        Self { q1_info, q2_info, q1, q2 }
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
        let f_of_g = if let Expr::Op { op: f_op, args: f_args,.. } = &a1[0] {
            if let Expr::Op { op: g_op, .. } = &a2[0] {
                Some(Expr::Op { op: f_op.clone(), args: vec![a2[0].clone()], ty: f_args[0].ty(), rel: None })
            } else { None }
        } else { None };

        if let Some(f_of_g_expr) = f_of_g {
            return (find_expr_in_relation(self.q1, &f_of_g_expr) && find_expr_in_relation(self.q2, &a1[0])) ||
                   (find_expr_in_relation(self.q2, &f_of_g_expr) && find_expr_in_relation(self.q1, &a1[0]));
        }
        false
    }
    
    fn filter_ref_attrs(&self, r1: VL, a1: &[Expr], r2: VL, a2: &[Expr]) -> bool {
        // LEFT JOIN vs INNER JOIN 또는 IN/EXISTS 유무 등 비대칭적 구조 확인
        let q1_has_left_join = has_specific_join(self.q1, &JoinKind::Left, r1, a1, r2, a2);
        let q2_has_inner_join = has_specific_join(self.q2, &JoinKind::Inner, r1, a1, r2, a2);
        q1_has_left_join && q2_has_inner_join // 가장 대표적인 케이스
        // TODO: IN/EXISTS 케이스 추가
    }

    fn filter_uniqueness(&self, r: VL, a: &[Expr]) -> bool {
        // 한쪽은 중복 가능성(self-join)이 있고 다른 쪽은 Distinct가 있는 비대칭 구조 확인
        let q1_has_self_join = has_self_join(self.q1, r);
        let q2_has_distinct = has_distinct(self.q2);
        (q1_has_self_join && !has_self_join(self.q2, r)) || (!q1_has_self_join && has_self_join(self.q2, r)) ||
        (q2_has_distinct && !has_distinct(self.q1)) || (!q2_has_distinct && has_distinct(self.q1))
    }

    fn filter_not_null(&self, r: VL, a: &[Expr]) -> bool {
        // 한쪽은 IS NOT NULL을 명시하고 다른 쪽은 그렇지 않은 비대칭 구조 확인
        let attr = &a[0];
        let q1_has_not_null = has_is_not_null_filter(self.q1, attr);
        let q2_lacks_not_null = !has_is_not_null_filter(self.q2, attr);
        (q1_has_not_null && q2_lacks_not_null) || (!q1_has_not_null && has_is_not_null_filter(self.q2, attr))
    }
}


// --- 필터링 규칙을 위한 재귀적 헬퍼 함수들 ---

fn find_expr_in_relation(rel: &URelation, target_expr: &Expr) -> bool {
    // ... AST를 순회하며 target_expr이 존재하는지 확인하는 로직 ...
    // 이 함수의 구현은 매우 복잡하므로, 여기서는 개념적인 존재만 명시합니다.
    // 실제로는 relation.rs에 이와 유사한 순회 함수를 추가해야 합니다.
    true // 임시로 항상 true 반환
}

fn has_specific_join(rel: &URelation, kind: &JoinKind, r1: VL, a1: &[Expr], r2: VL, a2: &[Expr]) -> bool {
    // ... AST를 순회하며 특정 조건을 만족하는 Join이 있는지 확인하는 로직 ...
    true // 임시
}

fn has_self_join(rel: &URelation, r: VL) -> bool {
    // ... AST를 순회하며 r을 self-join하는 패턴이 있는지 확인하는 로직 ...
    false // 임시
}

fn has_distinct(rel: &URelation) -> bool {
    matches!(rel, URelation::Distinct(_))
}

fn has_is_not_null_filter(rel: &URelation, attr: &Expr) -> bool {
    // ... AST를 순회하며 특정 속성에 대한 IS NOT NULL 필터가 있는지 확인하는 로직 ...
    false // 임시
}
