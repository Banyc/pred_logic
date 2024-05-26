use std::{collections::HashMap, sync::Arc};

use crate::expr::{Expr, Var};

pub type VarExprMap = HashMap<Var, Arc<Expr>>;

/// Return captured expressions referred by variables in the pattern
pub fn extract(src: &Arc<Expr>, pattern: &Expr) -> Option<VarExprMap> {
    match (src.as_ref(), pattern) {
        (_, Expr::Var(var)) => {
            let map = VarExprMap::from_iter([(var.clone(), Arc::clone(src))]);
            Some(map)
        }
        (Expr::Pred(s), Expr::Pred(p)) => {
            let same_name = s.name == p.name;
            let same_ind = s.ind == p.ind;
            if same_name && same_ind {
                Some(VarExprMap::new())
            } else {
                None
            }
        }
        (Expr::BinOp(s), Expr::BinOp(p)) => {
            let same_op = s.op == p.op;
            let left = extract(&s.left, &p.left);
            let right = extract(&s.right, &p.right);
            match (same_op, left, right) {
                (true, Some(left), Some(right)) => merge(left, right),
                _ => None,
            }
        }
        (Expr::UnOp(s), Expr::UnOp(p)) => {
            let same_op = s.op == p.op;
            let expr = extract(&s.expr, &p.expr);
            match (same_op, expr) {
                (true, Some(expr)) => Some(expr),
                _ => None,
            }
        }
        (Expr::EquivInd(s), Expr::EquivInd(p)) => {
            let same_equiv = s == p;
            if same_equiv {
                Some(VarExprMap::new())
            } else {
                None
            }
        }
        (Expr::Var(_), _) => None,
        _ => None,
    }
}

/// Merge two variable-to-expression tables together if the same variables refer to the same expressions
pub fn merge(mut left: VarExprMap, right: VarExprMap) -> Option<VarExprMap> {
    for (k, r) in right {
        match left.get(&k) {
            Some(l) => {
                if *l != r {
                    return None;
                }
            }
            None => {
                left.insert(k, r);
            }
        }
    }
    Some(left)
}
