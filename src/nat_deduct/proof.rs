use std::{collections::HashMap, sync::Arc};

use crate::{
    expr::{Expr, UnnamedGen, Var},
    extract::{self, extract},
};

use super::{
    and, not,
    r#impl::{addition, simplification, Syllogism},
    repl::{self, ReplacementOp},
};

#[derive(Debug, Clone)]
pub struct Proof {
    unnamed_space: UnnamedGen,
    premises: Vec<Arc<Expr>>,
    conclusion: Arc<Expr>,
}
impl Proof {
    pub fn new(premises: Vec<Arc<Expr>>, conclusion: Arc<Expr>) -> Self {
        let unnamed_space = UnnamedGen::new();
        Self {
            unnamed_space,
            premises,
            conclusion,
        }
    }

    pub fn premises(&self) -> &Vec<Arc<Expr>> {
        &self.premises
    }
    pub fn conclusion(&self) -> &Arc<Expr> {
        &self.conclusion
    }
    pub fn unnamed_space(&self) -> &UnnamedGen {
        &self.unnamed_space
    }

    pub fn syllogism(&mut self, major_prem: usize, minor_prem: usize) {
        let major_prem = &self.premises[major_prem];
        let minor_prem = &self.premises[minor_prem];
        let syllogism = Syllogism {
            major_prem,
            minor_prem,
        };
        let new = syllogism.any(self.unnamed_space.clone());
        self.premises.push(new);
    }

    pub fn addition(&mut self, prem: usize, new: Arc<Expr>) {
        let prem = &self.premises[prem];
        let Some(expr) = addition(prem, new) else {
            return;
        };
        self.premises.push(expr);
    }

    pub fn simplification(&mut self, prem: usize) {
        let prem = &self.premises[prem];
        let Some(expr) = simplification(prem, self.unnamed_space.clone()) else {
            return;
        };
        self.premises.push(expr);
    }

    pub fn replace(&mut self, prem: usize, pat: &Arc<Expr>, var: Var, op: ReplacementOp) {
        let prem = &self.premises[prem];
        let Some(captured) = extract(prem, pat) else {
            return;
        };
        let Some(expr) = captured.get(&var) else {
            return;
        };
        let Some(equiv) = repl::replace(expr, op, self.unnamed_space.clone()) else {
            return;
        };
        let map = HashMap::from_iter([(var, equiv)]);
        let new = extract::replace(pat, &map);
        self.premises.push(new);
    }

    pub fn conclude(&self) -> bool {
        self.premises.contains(&self.conclusion)
    }
}

pub fn contradiction(expr: &Arc<Expr>, mut unnamed_space: UnnamedGen) -> bool {
    let p = Var::Unnamed(unnamed_space.gen());
    let p_expr = Arc::new(Expr::Var(p.clone()));
    let contradiction = and(Arc::clone(&p_expr), not(p_expr));
    extract(expr, &contradiction).is_some()
}

#[cfg(test)]
mod tests {
    use crate::nat_deduct::{if_p_q, tests::named_var_expr};

    use super::*;

    #[test]
    fn test_proof_impl() {
        let a = named_var_expr("A");
        let b = named_var_expr("B");
        let c = named_var_expr("C");
        let premises = [
            if_p_q(a.clone(), not(b.clone())),
            if_p_q(c.clone(), b.clone()),
            a.clone(),
        ]
        .into();
        let conclusion = not(c.clone());
        let mut proof = Proof::new(premises, conclusion);
        print_premises(proof.premises());
        println!("// {}", proof.conclusion());
        println!();
        proof.syllogism(0, 2);
        print_premises(proof.premises());
        println!();
        proof.syllogism(1, 3);
        print_premises(proof.premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_proof_repl() {
        let a = named_var_expr("A");
        let b = named_var_expr("B");
        let c = named_var_expr("C");
        let premises = [
            if_p_q(a.clone(), not(and(b.clone(), c.clone()))),
            and(a.clone(), c.clone()),
        ]
        .into();
        let conclusion = not(b.clone());
        let mut proof = Proof::new(premises, conclusion);
        print_premises(proof.premises());
        println!("// {}", proof.conclusion());
        println!();
        proof.simplification(1);
        print_premises(proof.premises());
        println!();
        proof.syllogism(0, 2);
        print_premises(proof.premises());
        println!();
        {
            let mut unnamed_space = proof.unnamed_space().clone();
            let x = Var::Unnamed(unnamed_space.gen());
            proof.replace(
                3,
                &Arc::new(Expr::Var(x.clone())),
                x,
                ReplacementOp::DeMorgen,
            );
        }
        print_premises(proof.premises());
        println!();
        {
            let mut unnamed_space = proof.unnamed_space().clone();
            let x = Var::Unnamed(unnamed_space.gen());
            proof.replace(
                1,
                &Arc::new(Expr::Var(x.clone())),
                x,
                ReplacementOp::Commutativity,
            );
        }
        print_premises(proof.premises());
        println!();
        proof.simplification(5);
        print_premises(proof.premises());
        println!();
        {
            let mut unnamed_space = proof.unnamed_space().clone();
            let x = Var::Unnamed(unnamed_space.gen());
            proof.replace(
                4,
                &Arc::new(Expr::Var(x.clone())),
                x,
                ReplacementOp::Commutativity,
            );
        }
        print_premises(proof.premises());
        println!();
        {
            let mut unnamed_space = proof.unnamed_space().clone();
            let x = Var::Unnamed(unnamed_space.gen());
            proof.replace(
                6,
                &Arc::new(Expr::Var(x.clone())),
                x,
                ReplacementOp::DoubleNegation,
            );
        }
        print_premises(proof.premises());
        println!();
        proof.syllogism(7, 8);
        print_premises(proof.premises());
        println!();
        assert!(proof.conclude());
    }

    fn print_premises(premises: &[Arc<Expr>]) {
        for (i, prem) in premises.iter().enumerate() {
            println!("{i}. {prem}");
        }
    }
}
