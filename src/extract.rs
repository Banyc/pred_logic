use std::{borrow::Cow, collections::HashMap, sync::Arc};

use crate::expr::{BinOpExpr, Expr, Ident, Ind, Pred, Quant, UnOpExpr, Var};

/// Return captured expressions referred by variables in the pattern
pub fn extract(src: &Arc<Expr>, pattern: &Expr) -> Option<SymMap> {
    match (src.as_ref(), pattern) {
        (_, Expr::Var(var)) => {
            let map = HashMap::from_iter([(var.clone(), Arc::clone(src))]);
            Some(SymMap::from_expr_map(map))
        }
        (Expr::Pred(s), Expr::Pred(p)) => {
            let same_name = s.name == p.name;
            let same_len = s.ind.len() == p.ind.len();
            if !same_name || !same_len {
                return None;
            }
            let mut map = SymMap::new();
            for (s, p) in s.ind.iter().zip(p.ind.iter()) {
                if !map.ind_insert(p.clone(), s.clone()) {
                    return None;
                }
            }
            Some(map)
        }
        (Expr::Ident(s), Expr::Ident(p)) => {
            let mut map = SymMap::new();
            if !map.ind_insert(p.left.clone(), s.left.clone()) {
                return None;
            }
            if !map.ind_insert(p.right.clone(), s.right.clone()) {
                return None;
            }
            Some(map)
        }
        (Expr::BinOp(s), Expr::BinOp(p)) => {
            let same_op = s.op == p.op;
            let left = extract(&s.left, &p.left);
            let right = extract(&s.right, &p.right);
            match (same_op, left, right) {
                (true, Some(left), Some(right)) => left.merge(right),
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
        (Expr::Quant(s), Expr::Quant(p)) => {
            let same_op = s.op == p.op;
            let ind = SymMap::from_ind_map(HashMap::from_iter([(p.ind(), s.ind())]));
            let expr = extract(&s.expr, &p.expr);
            match (same_op, expr) {
                (true, Some(expr)) => expr.merge(ind),
                _ => None,
            }
        }
        (Expr::Var(_), _) => None,
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct SymMap {
    expr: HashMap<Var, Arc<Expr>>,
    ind: HashMap<Ind, Ind>,
}
impl SymMap {
    pub fn new() -> Self {
        Self {
            expr: HashMap::new(),
            ind: HashMap::new(),
        }
    }
    pub fn from_expr_map(expr: HashMap<Var, Arc<Expr>>) -> Self {
        Self {
            expr,
            ind: HashMap::new(),
        }
    }
    pub fn from_ind_map(ind: HashMap<Ind, Ind>) -> Self {
        Self {
            expr: HashMap::new(),
            ind,
        }
    }

    pub fn expr(&self) -> &HashMap<Var, Arc<Expr>> {
        &self.expr
    }
    pub fn force_insert_expr(&mut self, key: Var, value: Arc<Expr>) {
        self.expr.insert(key, value);
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
impl Default for SymMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Replace variables to given expressions.
/// Replace individuals.
pub fn replace(src: &Arc<Expr>, map: Cow<'_, SymMap>) -> Arc<Expr> {
    match src.as_ref() {
        Expr::Var(x) => {
            let Some(expr) = map.expr().get(x) else {
                return Arc::clone(src);
            };
            Arc::clone(expr)
        }
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
            left: replace(&x.left, map.clone()),
            right: replace(&x.right, map.clone()),
        })),
        Expr::UnOp(x) => Arc::new(Expr::UnOp(UnOpExpr {
            op: x.op.clone(),
            expr: replace(&x.expr, map.clone()),
        })),
        Expr::Quant(x) => {
            // // Protect its variable from being replaced
            // let mut map = map.into_owned();
            // map.ind_remove(&x.ind());
            // Arc::new(Expr::Quant(Quant {
            //     op: x.op.clone(),
            //     var: x.var.clone(),
            //     expr: replace(&x.expr, Cow::Owned(map)),
            // }))
            let var = match map.ind_get_ind(&x.ind()) {
                Some(ind) => match ind {
                    Ind::Const(_) => x.var.clone(),
                    Ind::Var(x) => x.clone(),
                },
                None => x.var.clone(),
            };
            Arc::new(Expr::Quant(Quant {
                op: x.op.clone(),
                var,
                expr: replace(&x.expr, map),
            }))
        }
    }
}
