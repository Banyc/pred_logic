use std::sync::Arc;

use crate::{
    constructors::{
        and, and_or, both_p_q_then_r, comm_and, comm_or, every, exists, ident, if_not_q_not_p,
        if_p_q, if_p_then_if_q_r, left_assoc_and, left_assoc_or, not, not_not, not_p_or, one_and,
        one_or, one_p, or, or_and, right_assoc_and, right_assoc_or, three_expanded_as_and_or,
        three_expanded_as_or_and, two_and_not, two_not_and, two_not_or, two_or_not,
    },
    expr::{Expr, Ident, QuantOp, UnOp, UnOpExpr, UnnamedGen, Var},
    subst::extract_expr,
};

#[derive(Debug, Clone)]
pub enum ReplacementOp {
    /// ```math
    /// ∼(p ⋅ q) :: (∼p ∨ ∼q) \\
    /// ∼(p ∨ q) :: (∼p ⋅ ∼q) \\
    /// ```
    DeMorgen,
    /// ```math
    /// (p ∨ q) :: (q ∨ p) \\
    /// (p ⋅ q) :: (q ⋅ p) \\
    /// ```
    Commutativity,
    /// ```math
    /// [p ∨ (q ∨ r)] :: [(p ∨ q) ∨ r] \\
    /// [p ⋅ (q ⋅ r)] :: [(p ⋅ q) ⋅ r] \\
    /// ```
    Associativity,
    /// ```math
    /// [p ⋅ (q ∨ r)] :: [(p ⋅ q) ∨ (p ⋅ r)] \\
    /// [p ∨ (q ⋅ r)] :: [(p ∨ q) ⋅ (p ∨ r)] \\
    /// ```
    Distribution,
    /// ```math
    /// p :: ∼∼p
    /// ```
    DoubleNegation,
    /// ```math
    /// (p ⊃ q) :: (∼q ⊃ ∼p)
    /// ```
    Transposition,
    /// ```math
    /// (p ⊃ q) :: (∼p ∨ q)
    /// ```
    MaterialImplication,
    /// ```math
    /// [(p ⋅ q) ⊃ r] :: [p ⊃ (q ⊃ r)]
    /// ```
    Exportation,
    /// ```math
    /// p :: (p ⋅ p)
    /// ```
    TautologyAnd,
    /// ```math
    /// p :: (p ∨ p)
    /// ```
    TautologyOr,
    /// ```math
    /// (x)Fx :: ∼(∃x)∼Fx
    /// (∃x)Fx :: ∼(x)∼Fx
    /// ```
    QuantifierNegationEvenNot,
    /// ```math
    /// ∼(x)Fx :: (∃x)∼Fx
    /// ∼(∃x)Fx :: (x)∼Fx
    /// ```
    QuantifierNegationOneNot,
}
pub fn replace(
    expr: &Arc<Expr>,
    op: ReplacementOp,
    unnamed_space: UnnamedGen,
) -> Option<Arc<Expr>> {
    match op {
        ReplacementOp::DeMorgen => de_morgen(expr, unnamed_space.clone()),
        ReplacementOp::Commutativity => commutativity(expr, unnamed_space.clone()),
        ReplacementOp::Associativity => associativity(expr, unnamed_space.clone()),
        ReplacementOp::Distribution => distribution(expr, unnamed_space.clone()),
        ReplacementOp::DoubleNegation => Some(double_negation(expr, unnamed_space.clone())),
        ReplacementOp::Transposition => transposition(expr, unnamed_space.clone()),
        ReplacementOp::MaterialImplication => material_implication(expr, unnamed_space.clone()),
        ReplacementOp::Exportation => exportation(expr, unnamed_space.clone()),
        ReplacementOp::TautologyAnd => Some(tautology_and(expr, unnamed_space.clone())),
        ReplacementOp::TautologyOr => Some(tautology_or(expr, unnamed_space.clone())),
        ReplacementOp::QuantifierNegationEvenNot => quantifier_negation_even_not(expr),
        ReplacementOp::QuantifierNegationOneNot => quantifier_negation_one_not(expr),
    }
}

macro_rules! replace {
    ( fn $f:ident ( $( $var:ident ),* ) {
        $patt:ident;
        $equiv:ident;
    } ) => {
        pub fn $f(expr: &Arc<Expr>, mut unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
            $( let $var = Var::Unnamed(unnamed_space.gen()); )*
            let patt = $patt(
                $( Arc::new(Expr::Prop($var.clone())), )*
            );
            let captured = extract_expr(expr, &patt)?;
            $( let $var = captured.expr().get(& $var).unwrap(); )*
            let equiv = $equiv(
                $( Arc::clone($var), )*
            );
            Some(equiv)
        }
    };
}

replace! (
    fn de_morgen_not_and(p, q) {
        two_not_and;
        two_or_not;
    }
);
replace! (
    fn de_morgen_or_not(p, q) {
        two_or_not;
        two_not_and;
    }
);
replace! (
    fn de_morgen_not_or(p, q) {
        two_not_or;
        two_and_not;
    }
);
replace! (
    fn de_morgen_and_not(p, q) {
        two_and_not;
        two_not_or;
    }
);
pub fn de_morgen(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        de_morgen_not_and(expr, unnamed_space.clone()),
        de_morgen_or_not(expr, unnamed_space.clone()),
        de_morgen_not_or(expr, unnamed_space.clone()),
        de_morgen_and_not(expr, unnamed_space.clone()),
    ) {
        (Some(x), _, _, _) | // _
        (_, Some(x), _, _) | // _
        (_, _, Some(x), _) | // _
        (_, _, _, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn commutativity_or(p, q) {
        or;
        comm_or;
    }
);
replace! (
    fn commutativity_and(p, q) {
        and;
        comm_and;
    }
);
pub fn commutativity_ident(expr: &Expr) -> Option<Arc<Expr>> {
    let Expr::Ident(Ident { left, right }) = expr else {
        return None;
    };
    Some(ident(right.clone(), left.clone()))
}
pub fn commutativity(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        commutativity_or(expr, unnamed_space.clone()),
        commutativity_and(expr, unnamed_space.clone()),
        commutativity_ident(expr),
    ) {
        (Some(x), _, _) | // _
        (_, Some(x), _) | // _
        (_, _, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn associativity_left_right_or(p, q, r) {
        left_assoc_or;
        right_assoc_or;
    }
);
replace! (
    fn associativity_right_left_or(p, q, r) {
        right_assoc_or;
        left_assoc_or;
    }
);
replace! (
    fn associativity_left_right_and(p, q, r) {
        left_assoc_and;
        right_assoc_and;
    }
);
replace! (
    fn associativity_right_left_and(p, q, r) {
        right_assoc_and;
        left_assoc_and;
    }
);
pub fn associativity(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        associativity_left_right_or(expr, unnamed_space.clone()),
        associativity_right_left_or(expr, unnamed_space.clone()),
        associativity_left_right_and(expr, unnamed_space.clone()),
        associativity_right_left_and(expr, unnamed_space.clone()),
    ) {
        (Some(x), _, _, _) | // _
        (_, Some(x), _, _) | // _
        (_, _, Some(x), _) | // _
        (_, _, _, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn distribution_expand_and(p, q, r) {
        and_or;
        three_expanded_as_or_and;
    }
);
replace! (
    fn distribution_collapse_or(p, q, r) {
        three_expanded_as_or_and;
        and_or;
    }
);
replace! (
    fn distribution_expand_or(p, q, r) {
        or_and;
        three_expanded_as_and_or;
    }
);
replace! (
    fn distribution_collapse_and(p, q, r) {
        three_expanded_as_and_or;
        or_and;
    }
);
pub fn distribution(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        distribution_expand_and(expr, unnamed_space.clone()),
        distribution_collapse_or(expr, unnamed_space.clone()),
        distribution_expand_or(expr, unnamed_space.clone()),
        distribution_collapse_and(expr, unnamed_space.clone()),
    ) {
        (Some(x), _, _, _) | // _
        (_, Some(x), _, _) | // _
        (_, _, Some(x), _) | // _
        (_, _, _, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn double_negation_empty(p) {
        one_p;
        not_not;
    }
);
replace! (
    fn double_negation_double(p) {
        not_not;
        one_p;
    }
);
pub fn double_negation(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Arc<Expr> {
    if let Some(x) = double_negation_double(expr, unnamed_space.clone()) {
        return x;
    }
    double_negation_empty(expr, unnamed_space.clone()).unwrap()
}

replace! (
    fn transposition_empty(p, q) {
        if_p_q;
        if_not_q_not_p;
    }
);
replace! (
    fn transposition_not(p, q) {
        if_not_q_not_p;
        if_p_q;
    }
);
pub fn transposition(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        transposition_empty(expr, unnamed_space.clone()),
        transposition_not(expr, unnamed_space.clone()),
    ) {
        (Some(x), _) | // _
        (_, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn material_implication_if(p, q) {
        if_p_q;
        not_p_or;
    }
);
replace! (
    fn material_implication_or(p, q) {
        not_p_or;
        if_p_q;
    }
);
pub fn material_implication(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        material_implication_if(expr, unnamed_space.clone()),
        material_implication_or(expr, unnamed_space.clone()),
    ) {
        (Some(x), _) | // _
        (_, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn exportation_and(p, q, r) {
        both_p_q_then_r;
        if_p_then_if_q_r;
    }
);
replace! (
    fn exportation_if(p, q, r) {
        if_p_then_if_q_r;
        both_p_q_then_r;
    }
);
pub fn exportation(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    match (
        exportation_and(expr, unnamed_space.clone()),
        exportation_if(expr, unnamed_space.clone()),
    ) {
        (Some(x), _) | // _
        (_, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

replace! (
    fn tautology_empty_and(p) {
        one_p;
        one_and;
    }
);
replace! (
    fn tautology_and_empty(p) {
        one_and;
        one_p;
    }
);
pub fn tautology_and(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Arc<Expr> {
    if let Some(x) = tautology_and_empty(expr, unnamed_space.clone()) {
        return x;
    }
    tautology_empty_and(expr, unnamed_space.clone()).unwrap()
}

replace! (
    fn tautology_empty_or(p) {
        one_p;
        one_or;
    }
);
replace! (
    fn tautology_or_empty(p) {
        one_or;
        one_p;
    }
);
pub fn tautology_or(expr: &Arc<Expr>, unnamed_space: UnnamedGen) -> Arc<Expr> {
    if let Some(x) = tautology_or_empty(expr, unnamed_space.clone()) {
        return x;
    }
    tautology_empty_or(expr, unnamed_space.clone()).unwrap()
}

pub fn quantifier_negation_empty(expr: &Expr) -> Option<Arc<Expr>> {
    let Expr::Quant(quant) = expr else {
        return None;
    };
    Some(match &quant.op {
        QuantOp::Every => not(exists(quant.var.clone(), not(Arc::clone(&quant.expr)))),
        QuantOp::Exists => not(every(quant.var.clone(), not(Arc::clone(&quant.expr)))),
    })
}
pub fn quantifier_negation_two_not(expr: &Expr) -> Option<Arc<Expr>> {
    let Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr,
    }) = expr
    else {
        return None;
    };
    let Expr::Quant(quant) = expr.as_ref() else {
        return None;
    };
    let Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr,
    }) = quant.expr.as_ref()
    else {
        return None;
    };
    Some(match &quant.op {
        QuantOp::Every => exists(quant.var.clone(), Arc::clone(expr)),
        QuantOp::Exists => every(quant.var.clone(), Arc::clone(expr)),
    })
}
pub fn quantifier_negation_even_not(expr: &Expr) -> Option<Arc<Expr>> {
    match (
        quantifier_negation_empty(expr),
        quantifier_negation_two_not(expr),
    ) {
        (Some(x), _) | // _
        (_, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

pub fn quantifier_negation_not_first(expr: &Expr) -> Option<Arc<Expr>> {
    let Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr,
    }) = expr
    else {
        return None;
    };
    let Expr::Quant(quant) = expr.as_ref() else {
        return None;
    };
    Some(match &quant.op {
        QuantOp::Every => exists(quant.var.clone(), not(Arc::clone(&quant.expr))),
        QuantOp::Exists => every(quant.var.clone(), not(Arc::clone(&quant.expr))),
    })
}
pub fn quantifier_negation_not_second(expr: &Expr) -> Option<Arc<Expr>> {
    let Expr::Quant(quant) = expr else {
        return None;
    };
    let Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr,
    }) = quant.expr.as_ref()
    else {
        return None;
    };
    Some(match &quant.op {
        QuantOp::Every => not(exists(quant.var.clone(), Arc::clone(expr))),
        QuantOp::Exists => not(every(quant.var.clone(), Arc::clone(expr))),
    })
}
pub fn quantifier_negation_one_not(expr: &Expr) -> Option<Arc<Expr>> {
    match (
        quantifier_negation_not_first(expr),
        quantifier_negation_not_second(expr),
    ) {
        (Some(x), _) | // _
        (_, Some(x)) => {
            Some(x)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::constructors::tests::named_var_expr;

    use super::*;

    #[test]
    fn test_dm_not_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = two_not_and(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼(p ⋅ q)");
        let unnamed_space = UnnamedGen::new();
        let equiv = de_morgen_not_and(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "∼p ∨ ∼q");
    }

    #[test]
    fn test_dm_or_not() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = two_or_not(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼p ∨ ∼q");
        let unnamed_space = UnnamedGen::new();
        let equiv = de_morgen_or_not(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "∼(p ⋅ q)");
    }

    #[test]
    fn test_dm_not_or() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = two_not_or(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼(p ∨ q)");
        let unnamed_space = UnnamedGen::new();
        let equiv = de_morgen_not_or(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "∼p ⋅ ∼q");
    }

    #[test]
    fn test_dm_and_not() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = two_and_not(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼p ⋅ ∼q");
        let unnamed_space = UnnamedGen::new();
        let equiv = de_morgen_and_not(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "∼(p ∨ q)");
    }

    #[test]
    fn test_com_or() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = or(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "p ∨ q");
        let unnamed_space = UnnamedGen::new();
        let equiv = commutativity_or(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "q ∨ p");
    }

    #[test]
    fn test_com_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = and(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "p ⋅ q");
        let unnamed_space = UnnamedGen::new();
        let equiv = commutativity_and(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "q ⋅ p");
    }

    #[test]
    fn test_assoc_left_right_or() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = left_assoc_or(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "(p ∨ q) ∨ r");
        let unnamed_space = UnnamedGen::new();
        let equiv = associativity_left_right_or(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "p ∨ (q ∨ r)");
    }

    #[test]
    fn test_assoc_right_left_or() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = right_assoc_or(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "p ∨ (q ∨ r)");
        let unnamed_space = UnnamedGen::new();
        let equiv = associativity_right_left_or(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "(p ∨ q) ∨ r");
    }

    #[test]
    fn test_assoc_left_right_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = left_assoc_and(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "(p ⋅ q) ⋅ r");
        let unnamed_space = UnnamedGen::new();
        let equiv = associativity_left_right_and(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "p ⋅ (q ⋅ r)");
    }

    #[test]
    fn test_assoc_right_left_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = right_assoc_and(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "p ⋅ (q ⋅ r)");
        let unnamed_space = UnnamedGen::new();
        let equiv = associativity_right_left_and(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "(p ⋅ q) ⋅ r");
    }

    #[test]
    fn test_dist_expand_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = and_or(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "p ⋅ (q ∨ r)");
        let unnamed_space = UnnamedGen::new();
        let equiv = distribution_expand_and(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "(p ⋅ q) ∨ (p ⋅ r)");
    }

    #[test]
    fn test_dist_collapse_or() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = three_expanded_as_or_and(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "(p ⋅ q) ∨ (p ⋅ r)");
        let unnamed_space = UnnamedGen::new();
        let equiv = distribution_collapse_or(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "p ⋅ (q ∨ r)");
    }

    #[test]
    fn test_dist_expand_or() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = or_and(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "p ∨ (q ⋅ r)");
        let unnamed_space = UnnamedGen::new();
        let equiv = distribution_expand_or(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "(p ∨ q) ⋅ (p ∨ r)");
    }

    #[test]
    fn test_dist_collapse_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let expr = three_expanded_as_and_or(Arc::clone(&p), Arc::clone(&q), Arc::clone(&r));
        println!("{expr}");
        assert_eq!(expr.to_string(), "(p ∨ q) ⋅ (p ∨ r)");
        let unnamed_space = UnnamedGen::new();
        let equiv = distribution_collapse_and(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "p ∨ (q ⋅ r)");
    }

    #[test]
    fn test_dn_empty() {
        let p = named_var_expr("p");
        let expr = p.clone();
        println!("{expr}");
        assert_eq!(expr.to_string(), "p");
        let unnamed_space = UnnamedGen::new();
        let equiv = double_negation_empty(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "∼∼p");
    }

    #[test]
    fn test_dn_double() {
        let p = named_var_expr("p");
        let expr = not_not(Arc::clone(&p));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼∼p");
        let unnamed_space = UnnamedGen::new();
        let equiv = double_negation_double(&expr, unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "p");
    }
}
