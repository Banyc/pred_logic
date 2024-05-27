use std::sync::Arc;

use crate::{
    expr::{Expr, UnnamedGen, Var},
    extract::{extract, merge, VarExprMap},
};

use super::{
    and, four_and_if, four_not_p_or_not_r, four_not_q_or_not_s, four_p_or_r, four_q_or_s, if_p_q,
    or, three_if_p_q, three_if_p_r, three_if_q_r, two_not_p, two_not_q, two_p, two_q,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Syllogism<'a> {
    pub major_prem: &'a Arc<Expr>,
    pub minor_prem: &'a Arc<Expr>,
}
macro_rules! syllogism_implication {
    ( fn $f:ident ( $( $var:ident ),* ) {
        $major_pat:ident;
        $minor_pat:ident;
        $conclusion:ident;
    } ) => {
        pub fn $f(&self, mut unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
            $( let $var = Var::Unnamed(unnamed_space.gen()); )*
            let major_pat = $major_pat(
                $( Arc::new(Expr::Var($var.clone())), )*
            );
            let minor_pat = $minor_pat(
                $( Arc::new(Expr::Var($var.clone())), )*
            );
            let captured = self.extract(&major_pat, &minor_pat)?;
            $( let $var = captured.get(& $var).unwrap(); )*
            let conclusion = $conclusion(
                $( Arc::clone($var), )*
            );
            Some(conclusion)
        }
    };
}
impl Syllogism<'_> {
    syllogism_implication!(
        fn modus_ponens(p, q) {
            if_p_q;
            two_p;
            two_q;
        }
    );
    syllogism_implication!(
        fn modus_tollens(p, q) {
            if_p_q;
            two_not_q;
            two_not_p;
        }
    );
    syllogism_implication!(
        fn pure_hypothetical_syllogism(p, q, r) {
            three_if_p_q;
            three_if_q_r;
            three_if_p_r;
        }
    );
    syllogism_implication!(
        fn disjunctive_syllogism(p, q) {
            or;
            two_not_p;
            two_q;
        }
    );
    syllogism_implication!(
        fn conjunctive_dilemma(p, q, r, s) {
            four_and_if;
            four_p_or_r;
            four_q_or_s;
        }
    );
    syllogism_implication!(
        fn disjunctive_dilemma(p, q, r, s) {
            four_and_if;
            four_not_q_or_not_s;
            four_not_p_or_not_r;
        }
    );

    pub fn conjunction(&self) -> Arc<Expr> {
        and(Arc::clone(self.major_prem), Arc::clone(self.minor_prem))
    }

    pub fn any(&self, unnamed_space: UnnamedGen) -> Arc<Expr> {
        if let Some(x) = self.modus_ponens(unnamed_space.clone()) {
            return x;
        }
        if let Some(x) = self.modus_tollens(unnamed_space.clone()) {
            return x;
        }
        if let Some(x) = self.pure_hypothetical_syllogism(unnamed_space.clone()) {
            return x;
        }
        if let Some(x) = self.disjunctive_syllogism(unnamed_space.clone()) {
            return x;
        }
        if let Some(x) = self.conjunctive_dilemma(unnamed_space.clone()) {
            return x;
        }
        if let Some(x) = self.disjunctive_dilemma(unnamed_space.clone()) {
            return x;
        }
        self.conjunction()
    }

    fn extract(&self, major_pattern: &Expr, minor_pattern: &Expr) -> Option<VarExprMap> {
        let captured_1 = extract(self.major_prem, major_pattern)?;
        let captured_2 = extract(self.minor_prem, minor_pattern)?;
        merge(captured_1, captured_2)
    }
}

pub fn simplification(prem: &Arc<Expr>, mut unnamed_space: UnnamedGen) -> Option<Arc<Expr>> {
    let p = Var::Unnamed(unnamed_space.gen());
    let q = Var::Unnamed(unnamed_space.gen());
    let p_expr = Arc::new(Expr::Var(p.clone()));
    let q_expr = Arc::new(Expr::Var(q.clone()));
    let pat = and(Arc::clone(&p_expr), Arc::clone(&q_expr));
    let captured = extract(prem, &pat)?;
    let conclusion = captured.get(&p).unwrap();
    Some(Arc::clone(conclusion))
}

pub fn addition(prem: &Arc<Expr>, q: Arc<Expr>) -> Option<Arc<Expr>> {
    let conclusion = or(Arc::clone(prem), q);
    Some(conclusion)
}

#[cfg(test)]
mod tests {
    use crate::nat_deduct::{not, tests::named_var_expr};

    use super::*;

    #[test]
    fn test_mp() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let major_prem = if_p_q(p.clone(), q.clone());
        let minor_prem = p.clone();
        println!("{major_prem}");
        println!("{minor_prem}");
        assert_eq!(major_prem.to_string(), "p ⊃ q");
        assert_eq!(minor_prem.to_string(), "p");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.modus_ponens(unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "q");
    }

    #[test]
    fn test_mt() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let major_prem = if_p_q(p.clone(), q.clone());
        let minor_prem = not(q.clone());
        println!("{major_prem}");
        println!("{minor_prem}");
        assert_eq!(major_prem.to_string(), "p ⊃ q");
        assert_eq!(minor_prem.to_string(), "∼q");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.modus_tollens(unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "∼p");
    }

    #[test]
    fn test_hs() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let major_prem = if_p_q(p.clone(), q.clone());
        let minor_prem = if_p_q(q.clone(), r.clone());
        println!("{major_prem}");
        println!("{minor_prem}");
        assert_eq!(major_prem.to_string(), "p ⊃ q");
        assert_eq!(minor_prem.to_string(), "q ⊃ r");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism
            .pure_hypothetical_syllogism(unnamed_space)
            .unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "p ⊃ r");
    }

    #[test]
    fn test_ds() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let major_prem = or(p.clone(), q.clone());
        let minor_prem = not(p.clone());
        println!("{major_prem}");
        println!("{minor_prem}");
        assert_eq!(major_prem.to_string(), "p ∨ q");
        assert_eq!(minor_prem.to_string(), "∼p");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.disjunctive_syllogism(unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "q");
    }

    #[test]
    fn test_cd() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let s = named_var_expr("s");
        let major_prem = four_and_if(p.clone(), q.clone(), r.clone(), s.clone());
        let minor_prem = or(p.clone(), r.clone());
        println!("{major_prem}");
        println!("{minor_prem}");
        assert_eq!(major_prem.to_string(), "(p ⊃ q) ⋅ (r ⊃ s)");
        assert_eq!(minor_prem.to_string(), "p ∨ r");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.conjunctive_dilemma(unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "q ∨ s");
    }

    #[test]
    fn test_dd() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let r = named_var_expr("r");
        let s = named_var_expr("s");
        let major_prem = four_and_if(p.clone(), q.clone(), r.clone(), s.clone());
        let minor_prem = or(not(q.clone()), not(s.clone()));
        println!("{major_prem}");
        println!("{minor_prem}");
        assert_eq!(major_prem.to_string(), "(p ⊃ q) ⋅ (r ⊃ s)");
        assert_eq!(minor_prem.to_string(), "∼q ∨ ∼s");
        let syllogism = Syllogism {
            major_prem: &major_prem,
            minor_prem: &minor_prem,
        };
        let unnamed_space = UnnamedGen::new();
        let conclusion = syllogism.disjunctive_dilemma(unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "∼p ∨ ∼r");
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
        let conclusion = syllogism.conjunction();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "p ⋅ q");
    }

    #[test]
    fn test_simp() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        let prem = and(p.clone(), q.clone());
        println!("{prem}");
        assert_eq!(prem.to_string(), "p ⋅ q");
        let unnamed_space = UnnamedGen::new();
        let conclusion = simplification(&prem, unnamed_space).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "p");
        assert_eq!(conclusion, p);
    }

    #[test]
    fn test_add() {
        let p = named_var_expr("p");
        let q = named_var_expr("q");
        println!("{p}");
        let conclusion = addition(&p, q.clone()).unwrap();
        println!("{conclusion}");
        assert_eq!(conclusion.to_string(), "p ∨ q");
    }
}
