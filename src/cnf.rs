use std::sync::Arc;

use crate::{
    constructors::{and, not, or},
    expr::{BinOp, BinOpExpr, Expr, UnOp, Var},
};

#[derive(Debug, Clone)]
pub struct ConjNormalForm {
    pub clauses: Vec<Clause>,
}
impl ConjNormalForm {
    pub fn merge(mut self, other: Self) -> Self {
        self.clauses.extend(other.clauses);
        self
    }
}
impl core::fmt::Display for ConjNormalForm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, clause) in self.clauses.iter().enumerate() {
            write!(f, "{}", clause.add_necessary_paren())?;
            if i + 1 < self.clauses.len() {
                write!(f, " ⋅ ")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
}
impl Clause {
    pub fn merge(mut self, other: Self) -> Self {
        self.literals.extend(other.literals);
        self
    }

    pub fn add_necessary_paren(&self) -> String {
        let this = self.to_string();
        if 1 < self.literals.len() {
            format!("({this})")
        } else {
            this
        }
    }
}
impl core::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, literal) in self.literals.iter().enumerate() {
            write!(f, "{literal}")?;
            if i + 1 < self.literals.len() {
                write!(f, " ∨ ")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Literal {
    pub not: bool,
    pub pred: Var,
}
impl core::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.not {
            write!(f, "∼")?;
        }
        write!(f, "{}", self.pred)
    }
}

#[derive(Debug, Clone)]
enum Component {
    Literal(Literal),
    Clause(Clause),
    Cnf(ConjNormalForm),
}
impl Component {
    pub fn into_literal(self) -> Option<Literal> {
        Some(match self {
            Component::Literal(x) => x,
            Component::Clause(_) | Component::Cnf(_) => return None,
        })
    }

    pub fn into_clause(self) -> Option<Clause> {
        Some(match self {
            Component::Literal(x) => Clause { literals: vec![x] },
            Component::Clause(x) => x,
            Component::Cnf(_) => return None,
        })
    }

    pub fn into_cnf(self) -> Option<ConjNormalForm> {
        Some(match self {
            Component::Clause(_) | Component::Literal(_) => ConjNormalForm {
                clauses: vec![self.into_clause()?],
            },
            Component::Cnf(x) => x,
        })
    }
}

pub fn conjunctive_normal_form(expr: &Arc<Expr>) -> Option<ConjNormalForm> {
    let expr = impl_to_disj(expr)?;
    let expr = neg_atom(&expr)?;
    let expr = conj_top(&expr)?;
    let comp = flatten(&expr)?;
    comp.into_cnf()
}

fn impl_to_disj(expr: &Arc<Expr>) -> Option<Arc<Expr>> {
    Some(match expr.as_ref() {
        Expr::Quant(_) | Expr::Pred(_) | Expr::Ident(_) => return None,
        Expr::BinOp(x) => {
            let left = impl_to_disj(&x.left)?;
            let right = impl_to_disj(&x.right)?;
            match x.op {
                BinOp::And => and(left, right),
                BinOp::Or => or(left, right),
                BinOp::If => or(not(left), right),
            }
        }
        Expr::UnOp(x) => {
            let expr = impl_to_disj(&x.expr)?;
            match x.op {
                UnOp::Not => not(expr),
            }
        }
        Expr::Prop(_) => Arc::clone(expr),
    })
}
fn neg_atom(expr: &Arc<Expr>) -> Option<Arc<Expr>> {
    Some(match expr.as_ref() {
        Expr::Quant(_) | Expr::Pred(_) | Expr::Ident(_) => return None,
        Expr::BinOp(x) => {
            let left = neg_atom(&x.left)?;
            let right = neg_atom(&x.right)?;
            match x.op {
                BinOp::And => and(left, right),
                BinOp::Or => or(left, right),
                BinOp::If => return None,
            }
        }
        Expr::UnOp(x) => {
            let UnOp::Not = &x.op;
            match x.expr.as_ref() {
                Expr::Quant(_) | Expr::Pred(_) | Expr::Ident(_) => return None,
                Expr::BinOp(x) => {
                    let left = neg_atom(&not(Arc::clone(&x.left)))?;
                    let right = neg_atom(&not(Arc::clone(&x.right)))?;
                    match x.op {
                        BinOp::And => or(left, right),
                        BinOp::Or => and(left, right),
                        BinOp::If => return None,
                    }
                }
                Expr::UnOp(x) => {
                    let UnOp::Not = &x.op;
                    neg_atom(&x.expr)?
                }
                Expr::Prop(_) => not(neg_atom(&x.expr).unwrap()),
            }
        }
        Expr::Prop(_) => Arc::clone(expr),
    })
}

fn conj_top(expr: &Arc<Expr>) -> Option<Arc<Expr>> {
    Some(match expr.as_ref() {
        Expr::Quant(_) | Expr::Pred(_) | Expr::Ident(_) => return None,
        Expr::BinOp(x) => match &x.op {
            BinOp::And => {
                let left = conj_top(&x.left)?;
                let right = conj_top(&x.right)?;
                and(left, right)
            }
            BinOp::Or => {
                let x_left = conj_top(&x.left)?;
                let x_right = conj_top(&x.right)?;
                if let Expr::BinOp(BinOpExpr {
                    op: BinOp::And,
                    left,
                    right,
                }) = x_left.as_ref()
                {
                    let left = or(Arc::clone(left), Arc::clone(&x_right));
                    let right = or(Arc::clone(right), Arc::clone(&x_right));
                    and(conj_top(&left)?, conj_top(&right)?)
                } else if let Expr::BinOp(BinOpExpr {
                    op: BinOp::And,
                    left,
                    right,
                }) = x_right.as_ref()
                {
                    let left = or(Arc::clone(&x_left), Arc::clone(left));
                    let right = or(Arc::clone(&x_left), Arc::clone(right));
                    and(conj_top(&left)?, conj_top(&right)?)
                } else {
                    or(x_left, x_right)
                }
            }
            BinOp::If => return None,
        },
        Expr::UnOp(_) | Expr::Prop(_) => Arc::clone(expr),
    })
}

fn flatten(expr: &Arc<Expr>) -> Option<Component> {
    Some(match expr.as_ref() {
        Expr::Quant(_) | Expr::Pred(_) | Expr::Ident(_) => return None,
        Expr::BinOp(x) => {
            let x_left = flatten(&x.left)?;
            let x_right = flatten(&x.right)?;
            match &x.op {
                BinOp::And => {
                    let left = x_left.into_cnf()?;
                    let right = x_right.into_cnf()?;
                    Component::Cnf(left.merge(right))
                }
                BinOp::Or => {
                    let left = x_left.into_clause()?;
                    let right = x_right.into_clause()?;
                    Component::Clause(left.merge(right))
                }
                BinOp::If => return None,
            }
        }
        Expr::UnOp(x) => {
            let UnOp::Not = &x.op;
            let expr = flatten(&x.expr)?.into_literal()?;
            let Literal { not: false, pred } = expr else {
                return None;
            };
            Component::Literal(Literal { not: true, pred })
        }
        Expr::Prop(x) => Component::Literal(Literal {
            not: false,
            pred: x.clone(),
        }),
    })
}

#[cfg(test)]
mod tests {
    use crate::constructors::{if_p_q, tests::named_var_expr};

    use super::*;

    #[test]
    fn test_double_negation() {
        let a = named_var_expr("a");
        let p = not(not(a));
        println!("{p}");
        assert_eq!(p.to_string(), "∼∼a");
        let q = neg_atom(&p).unwrap();
        println!("{q}");
        assert_eq!(q.to_string(), "a");
    }

    #[test]
    fn test_conj_top() {
        let a = named_var_expr("a");
        let b = named_var_expr("b");
        let c = named_var_expr("c");
        let d = named_var_expr("d");
        let e = named_var_expr("e");
        let f = named_var_expr("f");
        let g = named_var_expr("g");
        let h = named_var_expr("h");
        let i = named_var_expr("i");
        let j = named_var_expr("j");
        let p = or(
            and(a, b),
            or(or(c, d), or(or(and(e, f), and(g, h)), and(i, j))),
        );
        println!("{p}");
        let q = conj_top(&p).unwrap();
        println!("{q}");
    }

    #[test]
    fn test_cnf() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let f = if_p_q(not(if_p_q(or(p.clone(), not(q)), r.clone())), and(p, r));
        println!("{f}");
        assert_eq!(f.to_string(), "∼((p ∨ ∼q) ⊃ r) ⊃ (p ⋅ r)");
        let expr = impl_to_disj(&f).unwrap();
        println!("{expr}");
        let expr = neg_atom(&expr).unwrap();
        println!("{expr}");
        let expr = conj_top(&expr).unwrap();
        println!("{expr}");
        let f_ = conjunctive_normal_form(&f).unwrap();
        println!("{f_}");
        assert_eq!(
            f_.to_string(),
            "(∼p ∨ r ∨ p) ⋅ (∼p ∨ r ∨ r) ⋅ (q ∨ r ∨ p) ⋅ (q ∨ r ∨ r)"
        );
    }
}
