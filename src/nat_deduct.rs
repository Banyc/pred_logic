use std::sync::Arc;

use crate::{
    expr::{BinOp, BinOpExpr, Expr, UnOp, UnOpExpr, UnnamedGen, Var},
    extract::{extract, merge, VarExprMap},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syllogism<'a> {
    pub major_prem: &'a Arc<Expr>,
    pub minor_prem: &'a Arc<Expr>,
}
impl Syllogism<'_> {
    pub fn modus_ponens(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let p_expr = Arc::new(Expr::Var(p.clone()));
        let q_expr = Arc::new(Expr::Var(q.clone()));
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::clone(&p_expr),
            right: Arc::clone(&q_expr),
        });
        let minor_prem = Arc::clone(&p_expr);
        let captured = self.extract(&major_prem, &minor_prem)?;
        let conclusion = captured.get(&q).unwrap();
        Some(Arc::clone(conclusion))
    }

    pub fn modus_tollens(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let p_expr = Arc::new(Expr::Var(p.clone()));
        let q_expr = Arc::new(Expr::Var(q.clone()));
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::clone(&p_expr),
            right: Arc::clone(&q_expr),
        });
        let minor_prem = Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: Arc::clone(&q_expr),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let p = captured.get(&p).unwrap();
        let conclusion = Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: Arc::clone(p),
        }));
        Some(conclusion)
    }

    pub fn pure_hypothetical_syllogism(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let r = Var::Unnamed(unnamed_space.gen());
        let p_expr = Arc::new(Expr::Var(p.clone()));
        let q_expr = Arc::new(Expr::Var(q.clone()));
        let r_expr = Arc::new(Expr::Var(r.clone()));
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::clone(&p_expr),
            right: Arc::clone(&q_expr),
        });
        let minor_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: Arc::clone(&q_expr),
            right: Arc::clone(&r_expr),
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
        let p_expr = Arc::new(Expr::Var(p.clone()));
        let q_expr = Arc::new(Expr::Var(q.clone()));
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: p_expr.clone(),
            right: q_expr.clone(),
        });
        let minor_prem = Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p_expr.clone(),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let conclusion = captured.get(&q).unwrap();
        Some(Arc::clone(conclusion))
    }

    pub fn conjunctive_dilemma(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let r = Var::Unnamed(unnamed_space.gen());
        let s = Var::Unnamed(unnamed_space.gen());
        let p_expr = Arc::new(Expr::Var(p.clone()));
        let q_expr = Arc::new(Expr::Var(q.clone()));
        let r_expr = Arc::new(Expr::Var(r.clone()));
        let s_expr = Arc::new(Expr::Var(s.clone()));
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&p_expr),
                right: Arc::clone(&q_expr),
            })),
            right: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&r_expr),
                right: Arc::clone(&s_expr),
            })),
        });
        let minor_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: Arc::clone(&p_expr),
            right: Arc::clone(&r_expr),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let q = captured.get(&q).unwrap();
        let s = captured.get(&s).unwrap();
        let conclusion = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: Arc::clone(q),
            right: Arc::clone(s),
        }));
        Some(conclusion)
    }

    pub fn disjunctive_dilemma(&self, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
        let mut unnamed_space = unnamed_space.clone();
        let p = Var::Unnamed(unnamed_space.gen());
        let q = Var::Unnamed(unnamed_space.gen());
        let r = Var::Unnamed(unnamed_space.gen());
        let s = Var::Unnamed(unnamed_space.gen());
        let p_expr = Arc::new(Expr::Var(p.clone()));
        let q_expr = Arc::new(Expr::Var(q.clone()));
        let r_expr = Arc::new(Expr::Var(r.clone()));
        let s_expr = Arc::new(Expr::Var(s.clone()));
        let major_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&p_expr),
                right: Arc::clone(&q_expr),
            })),
            right: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&r_expr),
                right: Arc::clone(&s_expr),
            })),
        });
        let minor_prem = Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: Arc::clone(&p_expr),
            })),
            right: Arc::new(Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: Arc::clone(&r_expr),
            })),
        });
        let captured = self.extract(&major_prem, &minor_prem)?;
        let q = captured.get(&q).unwrap();
        let s = captured.get(&s).unwrap();
        let conclusion = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: Arc::clone(q),
            })),
            right: Arc::new(Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: Arc::clone(s),
            })),
        }));
        Some(conclusion)
    }

    pub fn conjunction(&self) -> Option<Arc<Expr>> {
        let conclusion = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::clone(self.major_prem),
            right: Arc::clone(self.minor_prem),
        }));
        Some(conclusion)
    }

    fn extract(&self, major_pattern: &Expr, minor_patter: &Expr) -> Option<VarExprMap> {
        let captured_1 = extract(self.major_prem, major_pattern)?;
        let captured_2 = extract(self.minor_prem, minor_patter)?;
        merge(captured_1, captured_2)
    }
}

pub fn simplification(prem: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
    let mut unnamed_space = unnamed_space.clone();
    let p = Var::Unnamed(unnamed_space.gen());
    let q = Var::Unnamed(unnamed_space.gen());
    let p_expr = Arc::new(Expr::Var(p.clone()));
    let q_expr = Arc::new(Expr::Var(q.clone()));
    let pat = Expr::BinOp(BinOpExpr {
        op: BinOp::And,
        left: Arc::clone(&p_expr),
        right: Arc::clone(&q_expr),
    });
    let captured = extract(prem, &pat)?;
    let conclusion = captured.get(&p).unwrap();
    Some(Arc::clone(conclusion))
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
        let minor_prem = p.clone();
        println!("{major_prem}");
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
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
        let minor_prem = Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: q.clone(),
        }));
        println!("{major_prem}");
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
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
        let minor_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::If,
            left: q.clone(),
            right: r.clone(),
        }));
        println!("{major_prem}");
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
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
        let minor_prem = Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p.clone(),
        }));
        println!("{major_prem}");
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.disjunctive_syllogism(&unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion, q);
    }

    #[test]
    fn test_cd() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let s = named_var_expr("s");
        let major_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&p),
                right: Arc::clone(&q),
            })),
            right: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&r),
                right: Arc::clone(&s),
            })),
        }));
        let minor_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: Arc::clone(&p),
            right: Arc::clone(&r),
        }));
        println!("{major_prem}");
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.conjunctive_dilemma(&unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(
            conclusion.as_ref(),
            &Expr::BinOp(BinOpExpr {
                op: BinOp::Or,
                left: q,
                right: s,
            })
        );
    }

    #[test]
    fn test_dd() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let s = named_var_expr("s");
        let major_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&p),
                right: Arc::clone(&q),
            })),
            right: Arc::new(Expr::BinOp(BinOpExpr {
                op: BinOp::If,
                left: Arc::clone(&r),
                right: Arc::clone(&s),
            })),
        }));
        let minor_prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::new(Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: Arc::clone(&p),
            })),
            right: Arc::new(Expr::UnOp(UnOpExpr {
                op: UnOp::Not,
                expr: Arc::clone(&r),
            })),
        }));
        println!("{major_prem}");
        println!("{minor_prem}");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.disjunctive_dilemma(&unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(
            conclusion.as_ref(),
            &Expr::BinOp(BinOpExpr {
                op: BinOp::And,
                left: Arc::new(Expr::UnOp(UnOpExpr {
                    op: UnOp::Not,
                    expr: q,
                })),
                right: Arc::new(Expr::UnOp(UnOpExpr {
                    op: UnOp::Not,
                    expr: s,
                })),
            })
        );
    }

    #[test]
    fn test_conj() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        println!("{p}");
        println!("{q}");
        let syllogism = Syllogism {
            major_prem: &p,
            minor_prem: &q,
        };
        let conclusion = syllogism.conjunction().unwrap();
        println!("{conclusion}");
        assert_eq!(
            conclusion.as_ref(),
            &Expr::BinOp(BinOpExpr {
                op: BinOp::And,
                left: p,
                right: q,
            })
        );
    }

    #[test]
    fn test_simp() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let prem = Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: Arc::clone(&p),
            right: Arc::clone(&q),
        }));
        println!("{prem}");
        let unnamed_space = UnnamedGen::new();
        let conclusion = simplification(&prem, &unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion, p);
    }

    fn named_var_expr(name: &str) -> Arc<Expr> {
        Arc::new(Expr::Var(Var::Named(Named { name: name.into() })))
    }
}
