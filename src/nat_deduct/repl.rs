use std::sync::Arc;

use crate::{
    expr::{Expr, UnnamedGen, Var},
    extract::extract,
};

use super::{
    and, and_or, comm_and, comm_or, left_assoc_and, left_assoc_or, not_not, one_p, or, or_and,
    right_assoc_and, right_assoc_or, three_expanded_as_and_or, three_expanded_as_or_and,
    two_and_not, two_not_and, two_not_or, two_or_not,
};

macro_rules! replace {
    ( fn $f:ident ( $( $var:ident ),* ) {
        $pat:ident;
        $equiv:ident;
    } ) => {
        pub fn $f(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
            let mut unnamed_space = unnamed_space.clone();
            $( let $var = Var::Unnamed(unnamed_space.gen()); )*
            let pat = $pat(
                $( Arc::new(Expr::Var($var.clone())), )*
            );
            let captured = extract(expr, &pat)?;
            $( let $var = captured.get(& $var).unwrap(); )*
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
pub fn de_morgen(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
    match (
        de_morgen_not_and(expr, unnamed_space),
        de_morgen_or_not(expr, unnamed_space),
        de_morgen_not_or(expr, unnamed_space),
        de_morgen_and_not(expr, unnamed_space),
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
pub fn commutativity(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
    match (
        commutativity_or(expr, unnamed_space),
        commutativity_and(expr, unnamed_space),
    ) {
        (Some(x), _) | // _
        (_, Some(x)) => {
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
pub fn associativity(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
    match (
        associativity_left_right_or(expr, unnamed_space),
        associativity_right_left_or(expr, unnamed_space),
        associativity_left_right_and(expr, unnamed_space),
        associativity_right_left_and(expr, unnamed_space),
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
pub fn distribution(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
    match (
        distribution_expand_and(expr, unnamed_space),
        distribution_collapse_or(expr, unnamed_space),
        distribution_expand_or(expr, unnamed_space),
        distribution_collapse_and(expr, unnamed_space),
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
pub fn double_negation(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
    match (
        // Try to cancel out the double nots first
        double_negation_double(expr, unnamed_space),
        double_negation_empty(expr, unnamed_space),
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
    use crate::nat_deduct::tests::named_var_expr;

    use super::*;

    #[test]
    fn test_dm_not_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = two_not_and(Arc::clone(&p), Arc::clone(&q));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼(p ⋅ q)");
        let unnamed_space = UnnamedGen::new();
        let equiv = de_morgen_not_and(&expr, &unnamed_space).unwrap();
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
        let equiv = de_morgen_or_not(&expr, &unnamed_space).unwrap();
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
        let equiv = de_morgen_not_or(&expr, &unnamed_space).unwrap();
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
        let equiv = de_morgen_and_not(&expr, &unnamed_space).unwrap();
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
        let equiv = commutativity_or(&expr, &unnamed_space).unwrap();
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
        let equiv = commutativity_and(&expr, &unnamed_space).unwrap();
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
        let equiv = associativity_left_right_or(&expr, &unnamed_space).unwrap();
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
        let equiv = associativity_right_left_or(&expr, &unnamed_space).unwrap();
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
        let equiv = associativity_left_right_and(&expr, &unnamed_space).unwrap();
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
        let equiv = associativity_right_left_and(&expr, &unnamed_space).unwrap();
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
        let equiv = distribution_expand_and(&expr, &unnamed_space).unwrap();
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
        let equiv = distribution_collapse_or(&expr, &unnamed_space).unwrap();
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
        let equiv = distribution_expand_or(&expr, &unnamed_space).unwrap();
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
        let equiv = distribution_collapse_and(&expr, &unnamed_space).unwrap();
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
        let equiv = double_negation_empty(&expr, &unnamed_space).unwrap();
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
        let equiv = double_negation_double(&expr, &unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "p");
    }
}
