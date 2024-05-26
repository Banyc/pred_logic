use std::sync::Arc;

use crate::{
    expr::{BinOp, BinOpExpr, Expr, UnOp, UnOpExpr, UnnamedGen, Var},
    extract::extract,
};

macro_rules! replace {
    ( $f:ident, $( $expr:ident )*, $pat:ident, $equiv:ident, ) => {
        pub fn $f(expr: &Arc<Expr>, unnamed_space: &UnnamedGen) -> Option<Arc<Expr>> {
            let mut unnamed_space = unnamed_space.clone();
            $( let $expr = Var::Unnamed(unnamed_space.gen()); )*
            let pat = $pat(
                $( Arc::new(Expr::Var($expr.clone())), )*
            );
            let captured = extract(expr, &pat)?;
            $( let $expr = captured.get(& $expr).unwrap(); )*
            let equiv = Arc::new($equiv(
                $( Arc::clone($expr), )*
            ));
            Some(equiv)
        }
    };
}

replace! (
    de_morgen_not_and,
    p q,
    not_and,
    or_not,
);
replace! (
    de_morgen_or_not,
    p q,
    or_not,
    not_and,
);
/// ```math
/// ∼(p ⋅ q)
/// ```
fn not_and(p: Arc<Expr>, q: Arc<Expr>) -> Expr {
    Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr: Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::And,
            left: p,
            right: q,
        })),
    })
}
/// ```math
/// ∼p ∨ ∼q
/// ```
fn or_not(p: Arc<Expr>, q: Arc<Expr>) -> Expr {
    Expr::BinOp(BinOpExpr {
        op: BinOp::Or,
        left: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p,
        })),
        right: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: q,
        })),
    })
}

replace! (
    de_morgen_not_or,
    p q,
    not_or,
    and_not,
);
replace! (
    de_morgen_and_not,
    p q,
    and_not,
    not_or,
);
/// ```math
/// ∼(p ∨ q)
/// ```
fn not_or(p: Arc<Expr>, q: Arc<Expr>) -> Expr {
    Expr::UnOp(UnOpExpr {
        op: UnOp::Not,
        expr: Arc::new(Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left: p,
            right: q,
        })),
    })
}
/// ```math
/// ∼p ⋅ ∼q
/// ```
fn and_not(p: Arc<Expr>, q: Arc<Expr>) -> Expr {
    Expr::BinOp(BinOpExpr {
        op: BinOp::And,
        left: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: p,
        })),
        right: Arc::new(Expr::UnOp(UnOpExpr {
            op: UnOp::Not,
            expr: q,
        })),
    })
}

#[cfg(test)]
mod tests {
    use crate::nat_deduct::tests::named_var_expr;

    use super::*;

    #[test]
    fn test_dm_not_and() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let expr = Arc::new(not_and(Arc::clone(&p), Arc::clone(&q)));
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
        let expr = Arc::new(or_not(Arc::clone(&p), Arc::clone(&q)));
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
        let expr = Arc::new(not_or(Arc::clone(&p), Arc::clone(&q)));
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
        let expr = Arc::new(and_not(Arc::clone(&p), Arc::clone(&q)));
        println!("{expr}");
        assert_eq!(expr.to_string(), "∼p ⋅ ∼q");
        let unnamed_space = UnnamedGen::new();
        let equiv = de_morgen_and_not(&expr, &unnamed_space).unwrap();
        println!("{equiv}");
        assert_eq!(equiv.to_string(), "∼(p ∨ q)");
    }
}
