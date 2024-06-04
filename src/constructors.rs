use std::sync::Arc;

use crate::expr::{BinOp, BinOpExpr, Expr, Ident, Ind, Quant, QuantOp, UnOp, UnOpExpr, Var};

/// ```math
/// ∼p
/// ```
pub fn not(p: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr: p,
    }))
}
/// ```math
/// ∼∼p
/// ```
pub fn not_not(p: Arc<Expr>) -> Arc<Expr> {
    not(not(p))
}
/// ```math
/// p
/// ```
pub fn one_p(p: Arc<Expr>) -> Arc<Expr> {
    p
}
/// ```math
/// p ⋅ p
/// ```
pub fn one_and(p: Arc<Expr>) -> Arc<Expr> {
    and(Arc::clone(&p), p)
}
/// ```math
/// p ∨ p
/// ```
pub fn one_or(p: Arc<Expr>) -> Arc<Expr> {
    or(Arc::clone(&p), p)
}

/// ```math
/// p ⊃ q
/// ```
pub fn if_p_q(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::If,
        left: p,
        right: q,
    }))
}
/// ```math
/// ∼q ⊃ ∼p
/// ```
pub fn if_not_q_not_p(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    if_p_q(not(q), not(p))
}
/// ```math
/// ∼p ∨ q
/// ```
pub fn not_p_or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    or(not(p), q)
}
/// ```math
/// p
/// ```
pub fn two_p(p: Arc<Expr>, _q: Arc<Expr>) -> Arc<Expr> {
    p
}
/// ```math
/// q
/// ```
pub fn two_q(_p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    q
}
/// ```math
/// ∼p
/// ```
pub fn two_not_p(p: Arc<Expr>, _q: Arc<Expr>) -> Arc<Expr> {
    not(p)
}
/// ```math
/// ∼q
/// ```
pub fn two_not_q(_p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    not(q)
}
/// ```math
/// ∼(p ⋅ q)
/// ```
pub fn two_not_and(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    not(and(p, q))
}
/// ```math
/// ∼p ∨ ∼q
/// ```
pub fn two_or_not(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    or(not(p), not(q))
}
/// ```math
/// ∼(p ∨ q)
/// ```
pub fn two_not_or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    not(or(p, q))
}
/// ```math
/// ∼p ⋅ ∼q
/// ```
pub fn two_and_not(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    and(not(p), not(q))
}
/// ```math
/// p ∨ q
/// ```
pub fn or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::Or,
        left: p,
        right: q,
    }))
}
/// ```math
/// q ∨ p
/// ```
pub fn comm_or(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    or(q, p)
}
/// ```math
/// p ⋅ q
/// ```
pub fn and(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::BinOp(BinOpExpr {
        op: BinOp::And,
        left: p,
        right: q,
    }))
}
/// ```math
/// q ⋅ p
/// ```
pub fn comm_and(p: Arc<Expr>, q: Arc<Expr>) -> Arc<Expr> {
    and(q, p)
}

/// ```math
/// p ∨ (q ∨ r)
/// ```
pub fn right_assoc_or(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    or(p, or(q, r))
}
/// ```math
/// (p ∨ q) ∨ r
/// ```
pub fn left_assoc_or(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    or(or(p, q), r)
}
/// ```math
/// p ⋅ (q ⋅ r)
/// ```
pub fn right_assoc_and(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    and(p, and(q, r))
}
/// ```math
/// (p ⋅ q) ⋅ r
/// ```
pub fn left_assoc_and(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    and(and(p, q), r)
}
/// ```math
/// p ⋅ (q ∨ r)
/// ```
pub fn and_or(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    and(p, or(q, r))
}
/// ```math
/// p ∨ (q ⋅ r)
/// ```
pub fn or_and(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    or(p, and(q, r))
}
/// ```math
/// p ⊃ q
/// ```
pub fn three_if_p_q(p: Arc<Expr>, q: Arc<Expr>, _r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(p, q)
}
/// ```math
/// q ⊃ r
/// ```
pub fn three_if_q_r(_p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(q, r)
}
/// ```math
/// p ⊃ r
/// ```
pub fn three_if_p_r(p: Arc<Expr>, _q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(p, r)
}
/// ```math
/// (p ⋅ q) ∨ (p ⋅ r)
/// ```
pub fn three_expanded_as_or_and(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    or(and(Arc::clone(&p), q), and(p, r))
}
/// ```math
/// (p ∨ q) ⋅ (p ∨ r)
/// ```
pub fn three_expanded_as_and_or(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    and(or(Arc::clone(&p), q), or(p, r))
}
/// ```math
/// (p ⋅ q) ⊃ r
/// ```
pub fn both_p_q_then_r(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(and(p, q), r)
}
/// ```math
/// p ⊃ (q ⊃ r)
/// ```
pub fn if_p_then_if_q_r(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>) -> Arc<Expr> {
    if_p_q(p, if_p_q(q, r))
}

/// ```math
/// (p ⊃ q) ⋅ (r ⊃ s)
/// ```
pub fn four_and_if(p: Arc<Expr>, q: Arc<Expr>, r: Arc<Expr>, s: Arc<Expr>) -> Arc<Expr> {
    and(if_p_q(p, q), if_p_q(r, s))
}
/// ```math
/// p ∨ r
/// ```
pub fn four_p_or_r(p: Arc<Expr>, _q: Arc<Expr>, r: Arc<Expr>, _s: Arc<Expr>) -> Arc<Expr> {
    or(p, r)
}
/// ```math
/// q ∨ s
/// ```
pub fn four_q_or_s(_p: Arc<Expr>, q: Arc<Expr>, _r: Arc<Expr>, s: Arc<Expr>) -> Arc<Expr> {
    or(q, s)
}
/// ```math
/// ∼q ∨ ∼s
/// ```
pub fn four_not_q_or_not_s(_p: Arc<Expr>, q: Arc<Expr>, _r: Arc<Expr>, s: Arc<Expr>) -> Arc<Expr> {
    or(not(q), not(s))
}
/// ```math
/// ∼p ∨ ∼r
/// ```
pub fn four_not_p_or_not_r(p: Arc<Expr>, _q: Arc<Expr>, r: Arc<Expr>, _s: Arc<Expr>) -> Arc<Expr> {
    or(not(p), not(r))
}

/// ```math
/// (x)p
/// ```
pub fn every(x: Var, p: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::Quant(Quant {
        op: QuantOp::Every,
        var: x,
        expr: p,
    }))
}
/// ```math
/// (∃x)p
/// ```
pub fn exists(x: Var, p: Arc<Expr>) -> Arc<Expr> {
    Arc::new(Expr::Quant(Quant {
        op: QuantOp::Exists,
        var: x,
        expr: p,
    }))
}

/// ```math
/// x = y
/// ```
pub fn ident(x: Ind, y: Ind) -> Arc<Expr> {
    Arc::new(Expr::Ident(Ident { left: x, right: y }))
}

#[cfg(test)]
pub mod tests {
    use std::sync::Arc;

    use crate::expr::{Expr, Named, Var};

    pub fn named_var_expr(name: &str) -> Arc<Expr> {
        var_expr(Var::Named(Named { name: name.into() }))
    }

    pub fn var_expr(var: Var) -> Arc<Expr> {
        Arc::new(Expr::Prop(var))
    }
}
