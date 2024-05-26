use std::sync::Arc;

use crate::expr::{BinOp, BinOpExpr, Expr, UnOp, UnOpExpr};

pub mod r#impl;
pub mod repl;

/// ```math
/// ∼p
/// ```
fn not(p: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr: p,
    }))
}

/// ```math
/// p ⊃ q
/// ```
fn if_p_q(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::If,
        left: p,
        right: q,
    }))
}
/// ```math
/// p
/// ```
fn two_p(p: Arc<Expr>, _q: Arc<Expr>) -> Arc<Expr> {
    p
}
/// ```math
/// q
/// ```
fn two_q(_p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    q
}
/// ```math
/// ∼p
/// ```
fn two_not_p(p: Arc<Expr>, _q: Arc<Expr>) -> Arc<Expr> {
    not(p)
}
/// ```math
/// ∼q
/// ```
fn two_not_q(_p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    not(q)
}
/// ```math
/// ∼(p ⋅ q)
/// ```
fn two_not_and(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr: Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: p,
            right: q,
        })),
    }))
}
/// ```math
/// ∼p ∨ ∼q
/// ```
fn two_or_not(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::Or,
        left: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p,
        })),
        right: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: q,
        })),
    }))
}
/// ```math
/// ∼(p ∨ q)
/// ```
fn two_not_or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr: Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: p,
            right: q,
        })),
    }))
}
/// ```math
/// ∼p ⋅ ∼q
/// ```
fn two_and_not(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::And,
        left: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p,
        })),
        right: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: q,
        })),
    }))
}
/// ```math
/// p ∨ q
/// ```
fn or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::Or,
        left: p,
        right: q,
    }))
}
/// ```math
/// q ∨ p
/// ```
fn comm_or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    or(q, p)
}
/// ```math
/// p ⋅ q
/// ```
fn and(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::And,
        left: p,
        right: q,
    }))
}
/// ```math
/// q ⋅ p
/// ```
fn comm_and(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    and(q, p)
}

/// ```math
/// p ⊃ q
/// ```
fn three_if_p_q(p: Arc<Expr>, q: Arc<Expr>, _r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(p, q)
}
/// ```math
/// q ⊃ r
/// ```
fn three_if_q_r(_p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(q, r)
}
/// ```math
/// p ⊃ r
/// ```
fn three_if_p_r(p: Arc<Expr>, _q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(p, r)
}

/// ```math
/// (p ⊃ q) ⋅ (r ⊃ s)
/// ```
fn four_and_if(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>, s: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::And,
        left: if_p_q(p, q),
        right: if_p_q(r, s),
    }))
}
/// ```math
/// p ∨ r
/// ```
fn four_p_or_r(p: Arc<Expr>, _q: Arc<Expr>, r: Arc<Expr>, _s: Arc<Expr>) -> Arc<Expr> {
    or(p, r)
}
/// ```math
/// q ∨ s
/// ```
fn four_q_or_s(_p: Arc<Expr>, q: Arc<Expr>, _r: Arc<Expr>, s: Arc<Expr>) -> Arc<Expr> {
    or(q, s)
}
/// ```math
/// ∼q ∨ ∼s
/// ```
fn four_not_q_or_not_s(_p: Arc<Expr>, q: Arc<Expr>, _r: Arc<Expr>, s: Arc<Expr>) -> Arc<Expr> {
    or(not(q), not(s))
}
/// ```math
/// ∼p ∨ ∼r
/// ```
fn four_not_p_or_not_r(p: Arc<Expr>, _q: Arc<Expr>, r: Arc<Expr>, _s: Arc<Expr>) -> Arc<Expr> {
    or(not(p), not(r))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::expr::{Expr, Named, Var};

    pub fn named_var_expr(name: &str) -> Arc<Expr> {
        Arc::new(Expr::Var(Var::Named(Named { name: name.into() })))
    }
}
