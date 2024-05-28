use std::{borrow::Cow, collections::HashMap, sync::Arc};

use crate::expr::{BinOpExpr, Expr, Ident, Ind, Pred, Quant, UnOpExpr, Var};

#[derive(Debug, Clone)]
pub struct ExprMap {
    expr: HashMap<Var, Arc<Expr>>,
}
impl ExprMap {
    pub fn new() -> Self {
        Self {
            expr: HashMap::new(),
        }
    }
    pub fn from_expr_map(expr: HashMap<Var, Arc<Expr>>) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> &HashMap<Var, Arc<Expr>> {
        &self.expr
    }
    pub fn force_insert_expr(&mut self, key: Var, value: Arc<Expr>) {
        self.expr.insert(key, value);
    }

    /// Merge two variable-to-expression tables together if the same variables refer to the same expressions
    pub fn merge(mut self, other: Self) -> Option<Self> {
        for (k, r) in other.expr {
            match self.expr.get(&k) {
                Some(l) => {
                    if *l != r {
                        return None;
                    }
                }
                None => {
                    self.expr.insert(k, r);
                }
            }
        }
        Some(self)
    }
}
impl Default for ExprMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Return captured expressions referred by variables in the pattern
pub fn extract_expr(src: &Arc<Expr>, pattern: &Expr) -> Option<ExprMap> {
    match (src.as_ref(), pattern) {
        (_, Expr::Var(var)) => {
            let map = HashMap::from_iter([(var.clone(), Arc::clone(src))]);
            Some(ExprMap::from_expr_map(map))
        }
        (Expr::Pred(_), Expr::Pred(_)) | (Expr::Ident(_), Expr::Ident(_)) => {
            if src.as_ref() == pattern {
                Some(ExprMap::new())
            } else {
                None
            }
        }
        (Expr::BinOp(s), Expr::BinOp(p)) => {
            let same_op = s.op == p.op;
            let left = extract_expr(&s.left, &p.left);
            let right = extract_expr(&s.right, &p.right);
            match (same_op, left, right) {
                (true, Some(left), Some(right)) => left.merge(right),
                _ => None,
            }
        }
        (Expr::UnOp(s), Expr::UnOp(p)) => {
            let same_op = s.op == p.op;
            let expr = extract_expr(&s.expr, &p.expr);
            match (same_op, expr) {
                (true, Some(expr)) => Some(expr),
                _ => None,
            }
        }
        (Expr::Quant(s), Expr::Quant(p)) => {
            let same_op = s.op == p.op;
            let same_var = s.var == p.var;
            let expr = extract_expr(&s.expr, &p.expr);
            match (same_op, same_var, expr) {
                (true, true, Some(expr)) => Some(expr),
                _ => None,
            }
        }
        (Expr::Var(_), _) => None,
        _ => None,
    }
}

/// Replace variables to given expressions.
pub fn replace_expr(src: &Arc<Expr>, map: Cow<'_, ExprMap>) -> Arc<Expr> {
    match src.as_ref() {
        Expr::Var(x) => {
            let Some(expr) = map.expr().get(x) else {
                return Arc::clone(src);
            };
            Arc::clone(expr)
        }
        Expr::Pred(_) | Expr::Ident(_) => Arc::clone(src),
        Expr::BinOp(x) => Arc::new(Expr::BinOp(BinOpExpr {
            op: x.op.clone(),
            left: replace_expr(&x.left, map.clone()),
            right: replace_expr(&x.right, map.clone()),
        })),
        Expr::UnOp(x) => Arc::new(Expr::UnOp(UnOpExpr {
            op: x.op.clone(),
            expr: replace_expr(&x.expr, map.clone()),
        })),
        Expr::Quant(x) => Arc::new(Expr::Quant(Quant {
            op: x.op.clone(),
            var: x.var.clone(),
            expr: replace_expr(&x.expr, map.clone()),
        })),
    }
}

#[derive(Debug, Clone)]
pub struct IndMap {
    ind: HashMap<Ind, Ind>,
}
impl IndMap {
    pub fn new() -> Self {
        Self {
            ind: HashMap::new(),
        }
    }
    pub fn from_ind_map(ind: HashMap<Ind, Ind>) -> Self {
        Self { ind }
    }

    /// `true`: successful
    #[must_use]
    pub fn ind_insert(&mut self, key: Ind, value: Ind) -> bool {
        match (&key, &value) {
            (Ind::Const(_), Ind::Const(_)) | (Ind::Var(_), Ind::Var(_)) => (),
            (Ind::Const(_), Ind::Var(_)) | (Ind::Var(_), Ind::Const(_)) => return false,
        }
        let Some(x) = self.ind.get(&key) else {
            self.ind.insert(key, value);
            return true;
        };
        x == &value
    }
    pub fn ind_get_ind(&self, k: &Ind) -> Option<Ind> {
        let ind = self.ind.get(k)?.clone();
        Some(ind)
    }
    pub fn ind_remove(&mut self, k: &Ind) {
        self.ind.remove(k);
    }

    /// Merge two tables together if the same individual refer to the same individual
    pub fn merge(mut self, other: Self) -> Option<Self> {
        for (k, r) in other.ind {
            match self.ind.get(&k) {
                Some(l) => {
                    if *l != r {
                        return None;
                    }
                }
                None => {
                    self.ind.insert(k, r);
                }
            }
        }
        Some(self)
    }
}
impl Default for IndMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Replace individuals.
pub fn replace_ind(src: &Arc<Expr>, map: Cow<'_, IndMap>) -> Arc<Expr> {
    match src.as_ref() {
        Expr::Var(_) => Arc::clone(src),
        Expr::Pred(x) => {
            let ind = &x.ind;
            let ind = ind
                .iter()
                .map(|x| match map.ind_get_ind(x) {
                    Some(x) => x,
                    None => x.clone(),
                })
                .collect::<Vec<Ind>>();
            let pred = Pred {
                name: Arc::clone(&x.name),
                ind,
            };
            Arc::new(Expr::Pred(pred))
        }
        Expr::Ident(x) => {
            let left = match map.ind_get_ind(&x.left) {
                Some(x) => x,
                None => x.left.clone(),
            };
            let right = match map.ind_get_ind(&x.right) {
                Some(x) => x,
                None => x.right.clone(),
            };
            let equiv_ind = Ident { left, right };
            Arc::new(Expr::Ident(equiv_ind))
        }
        Expr::BinOp(x) => Arc::new(Expr::BinOp(BinOpExpr {
            op: x.op.clone(),
            left: replace_ind(&x.left, map.clone()),
            right: replace_ind(&x.right, map.clone()),
        })),
        Expr::UnOp(x) => Arc::new(Expr::UnOp(UnOpExpr {
            op: x.op.clone(),
            expr: replace_ind(&x.expr, map.clone()),
        })),
        Expr::Quant(x) => {
            // Protect its variable from being replaced
            let mut map = map.into_owned();
            map.ind_remove(&x.ind());
            Arc::new(Expr::Quant(Quant {
                op: x.op.clone(),
                var: x.var.clone(),
                expr: replace_ind(&x.expr, Cow::Owned(map)),
            }))
            // let var = match map.ind_get_ind(&x.ind()) {
            //     Some(ind) => match ind {
            //         Ind::Const(_) => x.var.clone(),
            //         Ind::Var(x) => x.clone(),
            //     },
            //     None => x.var.clone(),
            // };
            // Arc::new(Expr::Quant(Quant {
            //     op: x.op.clone(),
            //     var,
            //     expr: replace(&x.expr, map),
            // }))
        }
    }
}
