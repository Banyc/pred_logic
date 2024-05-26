use std::sync::Arc;

use crate::{
    expr::{Expr, UnnamedGen, Var},
    extract::extract,
};

use super::{and, comm_and, comm_or, or, two_and_not, two_not_and, two_not_or, two_or_not};

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
    fn commutative_or(p, q) {
        or;
        comm_or;
    }
);
replace! (
    fn commutative_and(p, q) {
        and;
        comm_and;
    }
);

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
        let equiv = commutative_or(&expr, &unnamed_space).unwrap();
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
        let equiv = commutative_and(&expr, &unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "q ⋅ p");
    }
}
