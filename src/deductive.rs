use std::sync::Arc;

use crate::{
    expr::{BinOp, BinOpExpr, Expr, UnOp, UnOpExpr, UnnamedGen, Var},
    extract::{extract, merge, VarExprMap},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syllogism {
    pub major_prem: Arc<Expr>,
    pub minor_prem: Arc<Expr>,
}
impl Syllogism {
    pub fn modus_ponens(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::new(Expr::Var(p.clone())),
            right: Arc::new(Expr::Var(q.clone())),
        });
        let minor_prem = Expr::Var(p.clone());
        let captured = self.extract(&major_prem, &minor_prem)?;
        let conclusion = captured.get(&q).unwrap();
        Some(Arc::clone(conclusion))
    }

    pub fn modus_tollens(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::new(Expr::Var(p.clone())),
            right: Arc::new(Expr::Var(q.clone())),
        });
        let minor_prem = Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: Arc::new(Expr::Var(q.clone())),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let p = captured.get(&p).unwrap();
        let conclusion = Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p.clone(),
        }));
        Some(conclusion)
    }

    pub fn pure_hypothetical_syllogism(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let r = Var::Unnamed(unnamed_space.gen());
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::new(Expr::Var(p.clone())),
            right: Arc::new(Expr::Var(q.clone())),
        });
        let minor_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::new(Expr::Var(q.clone())),
            right: Arc::new(Expr::Var(r.clone())),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let p = captured.get(&p).unwrap();
        let r = captured.get(&r).unwrap();
        let conclusion = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::clone(p),
            right: Arc::clone(r),
        }));
        Some(conclusion)
    }

    pub fn disjunctive_syllogism(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: Arc::new(Expr::Var(p.clone())),
            right: Arc::new(Expr::Var(q.clone())),
        });
        let minor_prem = Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: Arc::new(Expr::Var(p.clone())),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let conclusion = captured.get(&q).unwrap();
        Some(Arc::clone(conclusion))
    }

    fn extract(&self, major_pattern: &Expr, minor_patter: &Expr) -> Option<VarExprMap> {
        let captured_1 = extract(&self.major_prem, major_pattern)?;
        let captured_2 = extract(&self.minor_prem, minor_patter)?;
        merge(captured_1, captured_2)
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
        let major_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: p.clone(),
            right: q.clone(),
        }));
        println!("{major_prem}");
        let minor_prem = p.clone();
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem,
            minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.modus_ponens(&unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion, q);
    }

    #[test]
    fn test_mt() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let major_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: p.clone(),
            right: q.clone(),
        }));
        println!("{major_prem}");
        let minor_prem = Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: q.clone(),
        }));
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem,
            minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.modus_tollens(&unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(
            conclusion.as_ref(),
            &Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: p.clone()
            })
        );
    }

    #[test]
    fn test_hs() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let major_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: p.clone(),
            right: q.clone(),
        }));
        println!("{major_prem}");
        let minor_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: q.clone(),
            right: r.clone(),
        }));
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem,
            minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism
            .pure_hypothetical_syllogism(&unnamed_space)
            .unwrap();
        println!("{conclusion}");
        assert_eq!(
            conclusion.as_ref(),
            &Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: p.clone(),
                right: r.clone(),
            })
        );
    }

    #[test]
    fn test_ds() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let major_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: p.clone(),
            right: q.clone(),
        }));
        println!("{major_prem}");
        let minor_prem = Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p.clone(),
        }));
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem,
            minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.disjunctive_syllogism(&unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion, q);
    }

    fn named_var_expr(name: &str) -> Arc<Expr> {
        Arc::new(Expr::Var(Var::Named(Named { name: name.into() })))
    }
}
