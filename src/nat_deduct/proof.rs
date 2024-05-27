use std::sync::Arc;

use crate::{
    expr::{Expr, UnnamedGen, Var},
    extract::extract,
};

use super::{
    and, not,
    r#impl::{addition, simplification, Syllogism},
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
    fn test_proof() {
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

    fn print_premises(premises: &[Arc<Expr>]) {
        for prem in premises {
            println!("{prem}");
        }
    }
}
