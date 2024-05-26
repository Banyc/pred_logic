use std::{collections::HashMap, sync::Arc};

use crate::expr::{BinOpExpr, Expr, UnOpExpr, Var};

pub type VarExprMap = HashMap<Var, Arc<Expr>>;

/// Return captured expressions referred by variables in the pattern
pub fn extract(src: &Arc<Expr>, pattern: &Expr) -> Option<VarExprMap> {
    match (src.as_ref(), pattern) {
        (_, Expr::Var(var)) => {
            let map = VarExprMap::from_iter([(var.clone(), Arc::clone(src))]);
            Some(map)
        }
        (Expr::Pred(_), Expr::Pred(_)) | (Expr::EquivInd(_), Expr::EquivInd(_)) => {
            if src.as_ref() == pattern {
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

/// Replace variables to given expressions
pub fn replace(src: &Arc<Expr>, map: &VarExprMap) -> Arc<Expr> {
    match src.as_ref() {
        Expr::Var(x) => {
            let Some(expr) = map.get(x) else {
                return Arc::clone(src);
            };
            Arc::clone(expr)
        }
        Expr::Pred(_) | Expr::EquivInd(_) => Arc::clone(src),
        Expr::BinOp(x) => Arc::new(Expr::BinOp(BinOpExpr {
            op: x.op.clone(),
            left: replace(&x.left, map),
            right: replace(&x.right, map),
        })),
        Expr::UnOp(x) => Arc::new(Expr::UnOp(UnOpExpr {
            op: x.op.clone(),
            expr: replace(&x.expr, map),
        })),
    }
}
