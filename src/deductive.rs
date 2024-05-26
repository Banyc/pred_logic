use std::sync::Arc;

use crate::{
    expr::{BinOp, BinOpExpr, Expr, UnnamedGen, Var},
    extract::{extract, merge},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syllogism {
    pub major_prem: Arc<Expr>,
    pub minor_prem: Arc<Expr>,
}
impl Syllogism {
    pub fn modus_ponens(&self, unnamed_space: &mut UnnamedGen) -> Option<Arc<Expr>> {
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let prem_1 = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::new(Expr::Var(p.clone())),
            right: Arc::new(Expr::Var(q.clone())),
        });
        let prem_2 = Expr::Var(p.clone());
        let captured_1 = extract(&self.major_prem, &prem_1)?;
        let captured_2 = extract(&self.minor_prem, &prem_2)?;
        let captured = merge(captured_1, captured_2)?;
        let conclusion = captured.get(&q).unwrap();
        Some(Arc::clone(conclusion))
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::Named;

    use super::*;

    #[test]
    fn test_mp() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let syllogism = Syllogism {
            major_prem: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: p.clone(),
                right: q.clone(),
            })),
            minor_prem: p.clone(),
        };
        let mut unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.modus_ponens(&mut unnamed_space);
        assert_eq!(conclusion.unwrap(), q);
    }

    fn named_var_expr(name: &str) -> Arc<Expr> {
        Arc::new(Expr::Var(Var::Named(Named { name: name.into() })))
    }
}
