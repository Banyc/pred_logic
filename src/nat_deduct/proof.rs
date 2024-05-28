use std::{borrow::Cow, collections::HashMap, sync::Arc};

use crate::{
    expr::{Expr, UnnamedGen, Var},
    extract::{self, extract, SymMap},
};

use super::{
    and, if_p_q, not,
    r#impl::{addition, simplification, Syllogism},
    repl::{self, ReplacementOp},
};

#[derive(Debug, Clone)]
pub enum Proof {
    Root(RootProof),
    Cond(CondProof),
    Indirect(IndirectProof),
}
impl Proof {
    pub fn deduction_mut(&mut self) -> &mut Deduction {
        match self {
            Proof::Root(x) => x.deduction_mut(),
            Proof::Cond(x) => x.deduction_mut(),
            Proof::Indirect(x) => x.deduction_mut(),
        }
    }
    pub fn deduction(&self) -> &Deduction {
        match self {
            Proof::Root(x) => x.deduction(),
            Proof::Cond(x) => x.deduction(),
            Proof::Indirect(x) => x.deduction(),
        }
    }
    pub fn root(&self) -> Option<&RootProof> {
        let Self::Root(x) = self else {
            return None;
        };
        Some(x)
    }
    pub fn cond(&self) -> Option<&CondProof> {
        let Self::Cond(x) = self else {
            return None;
        };
        Some(x)
    }
    pub fn indirect(&self) -> Option<&IndirectProof> {
        let Self::Indirect(x) = self else {
            return None;
        };
        Some(x)
    }
}

#[derive(Debug, Clone)]
pub struct RootProof {
    deduction: Deduction,
    conclusion: Arc<Expr>,
}
impl RootProof {
    pub fn new(premises: Vec<Arc<Expr>>, conclusion: Arc<Expr>) -> Self {
        let unnamed_space = UnnamedGen::new();
        let deduction = Deduction::new(premises, unnamed_space);
        Self {
            deduction,
            conclusion,
        }
    }

    pub fn deduction(&self) -> &Deduction {
        &self.deduction
    }
    pub fn deduction_mut(&mut self) -> &mut Deduction {
        &mut self.deduction
    }
    pub fn conclusion(&self) -> &Arc<Expr> {
        &self.conclusion
    }

    pub fn conclude(&self) -> bool {
        self.deduction().premises.contains(&self.conclusion)
    }
}

#[derive(Debug, Clone)]
pub struct Deduction {
    unnamed_space: UnnamedGen,
    premises: Vec<Arc<Expr>>,
}
impl Deduction {
    pub fn new(premises: Vec<Arc<Expr>>, unnamed_space: UnnamedGen) -> Self {
        Self {
            unnamed_space,
            premises,
        }
    }

    pub fn premises(&self) -> &Vec<Arc<Expr>> {
        &self.premises
    }
    pub fn unnamed_space(&self) -> &UnnamedGen {
        &self.unnamed_space
    }
    pub fn push_premise(&mut self, prem: Arc<Expr>, unnamed_space: Option<UnnamedGen>) {
        self.premises.push(prem);
        if let Some(x) = unnamed_space {
            self.unnamed_space = x;
        }
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
        let Some(expr) = simplification(prem) else {
            return;
        };
        self.premises.push(expr);
    }

    pub fn replace(&mut self, prem: usize, pat: impl Fn(Var) -> Arc<Expr>, op: ReplacementOp) {
        let mut unnamed_space = self.unnamed_space.clone();
        let var = Var::Unnamed(unnamed_space.gen());
        let pat = pat(var.clone());

        let prem = &self.premises[prem];
        let Some(captured) = extract(prem, &pat) else {
            return;
        };
        let Some(expr) = captured.expr().get(&var) else {
            return;
        };
        let Some(equiv) = repl::replace(expr, op, self.unnamed_space.clone()) else {
            return;
        };
        let map = SymMap::from_expr_map(HashMap::from_iter([(var, equiv)]));
        let new = extract::replace(&pat, Cow::Borrowed(&map));
        self.premises.push(new);
    }
}

#[derive(Debug, Clone)]
pub struct CondProof {
    prev_proof: Box<Proof>,
    deduction: Deduction,
    assume: Arc<Expr>,
}
impl CondProof {
    pub fn new(prev_proof: Box<Proof>, assume: Arc<Expr>) -> Self {
        let mut deduction = prev_proof.deduction().clone();
        deduction.push_premise(Arc::clone(&assume), None);
        Self {
            prev_proof,
            deduction,
            assume,
        }
    }

    pub fn deduction(&self) -> &Deduction {
        &self.deduction
    }
    pub fn deduction_mut(&mut self) -> &mut Deduction {
        &mut self.deduction
    }

    pub fn conclude(mut self) -> Proof {
        let last = self.deduction().premises().last().unwrap();
        let cond = if_p_q(Arc::clone(&self.assume), Arc::clone(last));
        let unnamed_space = self.deduction.unnamed_space().clone();
        self.prev_proof
            .deduction_mut()
            .push_premise(cond, Some(unnamed_space));
        *self.prev_proof
    }
}

#[derive(Debug, Clone)]
pub struct IndirectProof {
    prev_proof: Box<Proof>,
    deduction: Deduction,
    assume: Arc<Expr>,
}
impl IndirectProof {
    pub fn new(prev_proof: Box<Proof>, assume: Arc<Expr>) -> Self {
        let mut deduction = prev_proof.deduction().clone();
        deduction.push_premise(Arc::clone(&assume), None);
        Self {
            prev_proof,
            deduction,
            assume,
        }
    }

    pub fn deduction(&self) -> &Deduction {
        &self.deduction
    }
    pub fn deduction_mut(&mut self) -> &mut Deduction {
        &mut self.deduction
    }

    pub fn conclude(mut self) -> Result<Proof, Self> {
        let last = self.deduction().premises().last().unwrap();
        let unnamed_space = self.deduction.unnamed_space().clone();
        if !contradiction(last, unnamed_space) {
            return Err(self);
        }
        self.prev_proof
            .deduction_mut()
            .push_premise(not(self.assume), None);
        Ok(*self.prev_proof)
    }
}

/// ```math
/// p ⋅ ∼p
/// ```
pub fn contradiction(expr: &Arc<Expr>, mut unnamed_space: UnnamedGen) -> bool {
    let p = Var::Unnamed(unnamed_space.gen());
    let p_expr = Arc::new(Expr::Var(p.clone()));
    let contradiction = and(Arc::clone(&p_expr), not(p_expr));
    extract(expr, &contradiction).is_some()
}

#[cfg(test)]
mod tests {
    use crate::nat_deduct::{
        if_p_q, or,
        tests::{named_var_expr, var_expr},
    };

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
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof.deduction_mut().syllogism(0, 2);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(1, 3);
        print_premises(proof.deduction().premises());
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
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof.deduction_mut().simplification(1);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(0, 2);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(3, var_expr, ReplacementOp::DeMorgen);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(1, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(5);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(4, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(6, var_expr, ReplacementOp::DoubleNegation);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(7, 8);
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_cond_proof() {
        let a = named_var_expr("A");
        let b = named_var_expr("B");
        let c = named_var_expr("C");
        let d = named_var_expr("D");
        let e = named_var_expr("E");
        let premises = [
            if_p_q(a.clone(), and(b.clone(), c.clone())),
            if_p_q(or(b.clone(), d.clone()), e.clone()),
        ]
        .into();
        let conclusion = if_p_q(a.clone(), e.clone());
        let proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        let mut proof = CondProof::new(Box::new(Proof::Root(proof)), a.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(0, 2);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(3);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().addition(4, d.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(1, 5);
        print_premises(proof.deduction().premises());
        println!();
        let proof = proof.conclude().root().unwrap().clone();
        print_premises(proof.deduction().premises());
        assert!(proof.conclude());
    }

    #[test]
    fn test_indirect_proof() {
        let a = named_var_expr("A");
        let b = named_var_expr("B");
        let c = named_var_expr("C");
        let d = named_var_expr("D");
        let premises = [
            if_p_q(or(a.clone(), b.clone()), and(c.clone(), d.clone())),
            if_p_q(c.clone(), not(d.clone())),
        ]
        .into();
        let conclusion = not(a.clone());
        let proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        let mut proof = IndirectProof::new(Box::new(Proof::Root(proof)), a.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().addition(2, b.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(0, 3);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(4);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(1, 5);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(4, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(7);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(8, 6);
        print_premises(proof.deduction().premises());
        println!();
        let proof = proof.conclude().unwrap().root().unwrap().clone();
        print_premises(proof.deduction().premises());
        assert!(proof.conclude());
    }

    #[test]
    fn test_logical_truth() {
        let p = named_var_expr("P");
        let q = named_var_expr("Q");
        let premises = [].into();
        let conclusion = if_p_q(p.clone(), if_p_q(q.clone(), p.clone()));
        let proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        let proof = CondProof::new(Box::new(Proof::Root(proof)), p.clone());
        print_premises(proof.deduction().premises());
        println!();
        let mut proof = CondProof::new(Box::new(Proof::Cond(proof)), q.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().addition(0, p.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(2, var_expr, ReplacementOp::TautologyOr);
        print_premises(proof.deduction().premises());
        println!();
        let proof = proof.conclude().cond().unwrap().clone();
        print_premises(proof.deduction().premises());
        println!();
        let proof = proof.conclude().root().unwrap().clone();
        print_premises(proof.deduction().premises());
        assert!(proof.conclude());
    }

    fn print_premises(premises: &[Arc<Expr>]) {
        for (i, prem) in premises.iter().enumerate() {
            println!("{i}. {prem}");
        }
    }
}
