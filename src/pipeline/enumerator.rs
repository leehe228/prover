use std::collections::{HashMap, HashSet};
use itertools::{Itertools, iproduct};
use crate::pipeline::relation::{Constraint, Expr};
use crate::pipeline::shared::{DataType, Schema, VL};
use crate::pipeline::QueryInfo;

pub struct ConstraintEnumerator;

impl ConstraintEnumerator {
    pub fn new() -> Self {
        ConstraintEnumerator
    }

    /// 분석된 쿼리 정보를 바탕으로 가능한 모든 제약 조건 후보를 생성합니다.
    pub fn enumerate(&self, info: &QueryInfo, schemas: &[Schema]) -> Vec<Constraint> {
        let mut constraints = Vec::new();

        constraints.extend(self.enumerate_rel_eq(info));
        constraints.extend(self.enumerate_attrs_eq(info, schemas));
        constraints.extend(self.enumerate_pred_eq(info));
        constraints.extend(self.enumerate_sub_attr(info));
        constraints.extend(self.enumerate_ref_attrs(info, schemas));
        constraints.extend(self.enumerate_uniqueness(info, schemas));
        constraints.extend(self.enumerate_not_null(info, schemas));

        constraints
    }

    /// Relation Equality 제약 조건 열거
    fn enumerate_rel_eq(&self, info: &QueryInfo) -> Vec<Constraint> {
        if info.relations.len() < 2 {
            return vec![];
        }
        info.relations.iter().cloned().combinations(2).map(|pair| {
            Constraint::RelEq { r1: VL(pair[0]), r2: VL(pair[1]) }
        }).collect()
    }

    /// Attribute Equality 제약 조건 열거
    fn enumerate_attrs_eq(&self, info: &QueryInfo, schemas: &[Schema]) -> Vec<Constraint> {
        if info.attributes.len() < 2 {
            return vec![];
        }
        info.attributes.iter().cloned().combinations(2).filter_map(|pair| {
            let (r1_idx, c1_idx) = pair[0];
            let (r2_idx, c2_idx) = pair[1];
            
            // 타입이 같은 속성끼리만 비교
            if schemas[r1_idx].types[c1_idx] == schemas[r2_idx].types[c2_idx] {
                Some(Constraint::AttrsEq {
                    a1: vec![Expr::Col { column: VL(c1_idx), ty: schemas[r1_idx].types[c1_idx].clone() }],
                    a2: vec![Expr::Col { column: VL(c2_idx), ty: schemas[r2_idx].types[c2_idx].clone() }],
                })
            } else {
                None
            }
        }).collect()
    }
    
    /// Predicate Equivalence 제약 조건 열거
    fn enumerate_pred_eq(&self, info: &QueryInfo) -> Vec<Constraint> {
        if info.predicates.len() < 2 {
            return vec![];
        }
        let predicates: Vec<_> = info.predicates.iter().cloned().collect();
        predicates.iter().combinations(2).flat_map(|p_pair| {
            // 술어는 특정 속성에 종속되지 않을 수 있으므로, 임의의 변수 하나를 인자로 사용
            let dummy_arg = Expr::Col { column: VL(0), ty: DataType::Integer };
            let p1 = Box::new(Expr::Op {
                op: p_pair[0].clone(),
                args: vec![dummy_arg.clone()],
                ty: DataType::Boolean,
                rel: None,
            });
            let p2 = Box::new(Expr::Op {
                op: p_pair[1].clone(),
                args: vec![dummy_arg],
                ty: DataType::Boolean,
                rel: None,
            });
            vec![Constraint::PredEq { p1, p2 }]
        }).collect()
    }

    /// Sub-Attribute Composition 제약 조건 열거
    fn enumerate_sub_attr(&self, info: &QueryInfo) -> Vec<Constraint> {
        if info.functions.len() < 2 {
            return vec![];
        }
        let functions: Vec<_> = info.functions.iter().cloned().collect();
        functions.iter().permutations(2).map(|p_pair| {
                // 함수 역시 특정 속성에 종속되지 않으므로, 임의의 변수를 인자로 사용
            let dummy_arg = Expr::Col { column: VL(0), ty: DataType::Integer }; // Assume functions take Integer
            let a1 = vec![Expr::Op { op: p_pair[0].clone(), args: vec![dummy_arg.clone()], ty: DataType::Integer, rel: None }];
            let a2 = vec![Expr::Op { op: p_pair[1].clone(), args: vec![dummy_arg], ty: DataType::Integer, rel: None }];
            Constraint::SubAttr { a1, a2 }
        }).collect()
    }

    /// Referential Attributes 제약 조건 열거
    fn enumerate_ref_attrs(&self, info: &QueryInfo, schemas: &[Schema]) -> Vec<Constraint> {
        if info.relations.len() < 2 {
            return vec![];
        }
        info.relations.iter().cloned().permutations(2).flat_map(|r_pair| {
            let r1_idx = r_pair[0];
            let r2_idx = r_pair[1];
            let r1_attrs = (0..schemas[r1_idx].types.len()).map(move |i| (i, schemas[r1_idx].types[i].clone()));
            let r2_attrs = (0..schemas[r2_idx].types.len()).map(move |i| (i, schemas[r2_idx].types[i].clone()));
            
            iproduct!(r1_attrs, r2_attrs).filter_map(move |((c1_idx, c1_type), (c2_idx, c2_type))| {
                if c1_type == c2_type {
                    Some(Constraint::RefAttrs {
                        r1: VL(r1_idx),
                        a1: vec![Expr::Col { column: VL(c1_idx), ty: c1_type.clone() }],
                        r2: VL(r2_idx),
                        a2: vec![Expr::Col { column: VL(c2_idx), ty: c2_type }],
                    })
                } else {
                    None
                }
            })
        }).collect()
    }

    /// Uniqueness 제약 조건 열거
    fn enumerate_uniqueness(&self, info: &QueryInfo, schemas: &[Schema]) -> Vec<Constraint> {
        info.relations.iter().flat_map(|&r_idx| {
            let num_attrs = schemas[r_idx].types.len();
            (1..=num_attrs).flat_map(move |k| {
                (0..num_attrs).combinations(k).map(move |col_indices| {
                    let attrs = col_indices.into_iter().map(|c_idx| {
                        Expr::Col { column: VL(c_idx), ty: schemas[r_idx].types[c_idx].clone() }
                    }).collect();
                    Constraint::Unique { r: VL(r_idx), a: attrs }
                })
            })
        }).collect()
    }

    /// Non-Null 제약 조건 열거
    fn enumerate_not_null(&self, info: &QueryInfo, schemas: &[Schema]) -> Vec<Constraint> {
        info.attributes.iter().map(|&(r_idx, c_idx)| {
            Constraint::NotNull {
                r: VL(r_idx),
                a: vec![Expr::Col { column: VL(c_idx), ty: schemas[r_idx].types[c_idx].clone() }],
            }
        }).collect()
    }
}
