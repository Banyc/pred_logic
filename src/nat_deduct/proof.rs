use std::{borrow::Cow, collections::HashSet, sync::Arc};

use crate::{
    expr::{Expr, Ind, UnnamedGen, Var},
    extract::{extract_expr, replace_expr},
};

use super::{
    and, if_p_q, not,
    r#impl::{
        addition, existential_generalization, existential_instantiation, simplification,
        universal_generalization, universal_instantiation, Syllogism,
    },
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
pub struct CondProof {
    prev_proof: Box<Proof>,
    deduction: Deduction,
    assume: Arc<Expr>,
}
impl CondProof {
    pub fn new(prev_proof: Box<Proof>, assume: Arc<Expr>) -> Self {
        let mut deduction = prev_proof.deduction().clone();
        deduction.push_premise(Arc::clone(&assume), None, PremiseType::Assumed);
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
        self.prev_proof.deduction_mut().push_premise(
            cond,
            Some(unnamed_space),
            PremiseType::Deducted,
        );
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
        deduction.push_premise(Arc::clone(&assume), None, PremiseType::Assumed);
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
            .push_premise(not(self.assume), None, PremiseType::Deducted);
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
    extract_expr(expr, &contradiction).is_some()
}

#[derive(Debug, Clone)]
pub enum PremiseType {
    Assumed,
    Deducted,
}

#[derive(Debug, Clone)]
pub struct Deduction {
    unnamed_space: UnnamedGen,
    premises: Vec<Arc<Expr>>,
    assumed_premises: Vec<usize>,
    free_variables_in_existential_instantiation: HashSet<Var>,
}
impl Deduction {
    pub fn new(premises: Vec<Arc<Expr>>, unnamed_space: UnnamedGen) -> Self {
        Self {
            unnamed_space,
            premises,
            assumed_premises: vec![],
            free_variables_in_existential_instantiation: HashSet::new(),
        }
    }

    pub fn premises(&self) -> &Vec<Arc<Expr>> {
        &self.premises
    }
    pub fn unnamed_space(&self) -> &UnnamedGen {
        &self.unnamed_space
    }
    pub fn push_premise(
        &mut self,
        prem: Arc<Expr>,
        unnamed_space: Option<UnnamedGen>,
        ty: PremiseType,
    ) {
        match ty {
            PremiseType::Assumed => {
                self.assumed_premises.push(self.premises.len());
            }
            PremiseType::Deducted => (),
        }
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
        let Some(mut captured) = extract_expr(prem, &pat) else {
            return;
        };
        println!("{pat}");
        println!("{captured:#?}");
        let Some(expr) = captured.expr().get(&var) else {
            return;
        };
        let Some(equiv) = repl::replace(expr, op, self.unnamed_space.clone()) else {
            return;
        };
        captured.force_insert_expr(var, equiv);
        let new = replace_expr(&pat, Cow::Borrowed(&captured));
        self.premises.push(new);
    }

    pub fn universal_instantiation(&mut self, prem: usize, ind: Ind) {
        let prem = &self.premises[prem];
        let Some(prem) = universal_instantiation(prem, ind) else {
            return;
        };
        self.premises.push(prem);
    }
    pub fn universal_generalization(&mut self, prem: usize, old: Var, new: Var) {
        if self.assumed_premises.contains(&prem) {
            return;
        }
        if self
            .free_variables_in_existential_instantiation
            .contains(&old)
        {
            return;
        }
        let prem = &self.premises[prem];
        let Some(prem) = universal_generalization(prem, old, new) else {
            return;
        };
        self.premises.push(prem);
    }
    pub fn existential_instantiation(&mut self, prem: usize) -> Option<Var> {
        let prem = &self.premises[prem];
        let (prem, var) = existential_instantiation(prem, &mut self.unnamed_space)?;
        self.free_variables_in_existential_instantiation
            .extend(prem.free_variables());
        self.premises.push(prem);
        Some(var)
    }
    pub fn existential_generalization(&mut self, prem: usize, old: Ind, new: Var) {
        let prem = &self.premises[prem];
        let Some(prem) = existential_generalization(prem, old, new) else {
            return;
        };
        self.premises.push(prem);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        expr::{Named, Pred},
        nat_deduct::{
            every, exists, if_p_q, or,
            tests::{named_var_expr, var_expr},
        },
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

    #[test]
    fn test_ui() {
        let x = named_var("x");
        let p = named_var("p");
        let x_ind = Ind::Var(x.clone());
        let p_ind = Ind::Const(p.clone());
        let e_x = singular_pred("E", x_ind.clone());
        let e_p = singular_pred("E", p_ind.clone());
        let s_x = singular_pred("S", x_ind.clone());
        let s_p = singular_pred("S", p_ind.clone());
        let premises = [
            every(x.clone(), if_p_q(e_x.clone(), s_x.clone())),
            e_p.clone(),
        ]
        .into();
        let conclusion = s_p.clone();
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(0, p_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(2, 1);
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_ug() {
        let x = named_var("x");
        let y = named_var("y");
        let x_ind = Ind::Var(x.clone());
        let y_ind = Ind::Var(y.clone());
        let p_x = singular_pred("P", x_ind.clone());
        let d_x = singular_pred("D", x_ind.clone());
        let c_x = singular_pred("C", x_ind.clone());
        let premises = [
            every(x.clone(), if_p_q(p_x.clone(), d_x.clone())),
            every(x.clone(), if_p_q(d_x.clone(), c_x.clone())),
        ]
        .into();
        let conclusion = every(x.clone(), if_p_q(p_x.clone(), c_x.clone()));
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(0, y_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(1, y_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(2, 3);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .universal_generalization(4, y.clone(), x.clone());
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_eg() {
        let x = named_var("x");
        let a = named_var("a");
        let x_ind = Ind::Var(x.clone());
        let a_ind = Ind::Const(a.clone());
        let t_x = singular_pred("T", x_ind.clone());
        let s_x = singular_pred("S", x_ind.clone());
        let t_a = singular_pred("T", a_ind.clone());
        let premises = [
            every(x.clone(), if_p_q(t_x.clone(), s_x.clone())),
            t_a.clone(),
        ]
        .into();
        let conclusion = exists(x.clone(), s_x.clone());
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(0, a_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(2, 1);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .existential_generalization(3, a_ind.clone(), x.clone());
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_ei() {
        let x = named_var("x");
        let x_ind = Ind::Var(x.clone());
        let a_x = singular_pred("A", x_ind.clone());
        let c_x = singular_pred("C", x_ind.clone());
        let g_x = singular_pred("G", x_ind.clone());
        let premises = [
            every(x.clone(), if_p_q(a_x.clone(), c_x.clone())),
            exists(x.clone(), and(a_x.clone(), g_x.clone())),
        ]
        .into();
        let conclusion = exists(x.clone(), and(g_x.clone(), c_x.clone()));
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        let a = proof.deduction_mut().existential_instantiation(1).unwrap();
        let a_ind = Ind::Const(a.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(0, a_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(2, var_expr, ReplacementOp::Commutativity);
        proof.deduction_mut().simplification(4);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(2);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(3, 6);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(5, 7);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .existential_generalization(8, a_ind.clone(), x.clone());
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_qn() {
        let x = named_var("x");
        let x_ind = Ind::Var(x.clone());
        let p_x = singular_pred("P", x_ind.clone());
        let q_x = singular_pred("Q", x_ind.clone());
        let r_x = singular_pred("R", x_ind.clone());
        let premises = [
            not(exists(x.clone(), and(p_x.clone(), not(q_x.clone())))),
            not(every(x.clone(), or(not(r_x.clone()), q_x.clone()))),
        ]
        .into();
        let conclusion = exists(x.clone(), not(p_x.clone()));
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof
            .deduction_mut()
            .replace(0, var_expr, ReplacementOp::QuantifierNegationOneNot);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().replace(
            2,
            |repl| every(x.clone(), var_expr(repl)),
            ReplacementOp::DeMorgen,
        );
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().replace(
            3,
            |repl| every(x.clone(), or(not(p_x.clone()), var_expr(repl))),
            ReplacementOp::DoubleNegation,
        );
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(1, var_expr, ReplacementOp::QuantifierNegationOneNot);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().replace(
            5,
            |repl| exists(x.clone(), var_expr(repl)),
            ReplacementOp::DeMorgen,
        );
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().replace(
            6,
            |repl| exists(x.clone(), and(var_expr(repl), not(q_x.clone()))),
            ReplacementOp::DoubleNegation,
        );
        print_premises(proof.deduction().premises());
        println!();
        let a = proof.deduction_mut().existential_instantiation(7).unwrap();
        let a_ind = Ind::Const(a);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(4, a_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(8, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(10);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(9, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(12, 11);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .existential_generalization(13, a_ind.clone(), x.clone());
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    fn named_var(name: &str) -> Var {
        Var::Named(Named { name: name.into() })
    }
    fn singular_pred(name: &str, ind: Ind) -> Arc<Expr> {
        Arc::new(Expr::Pred(Pred {
            name: name.into(),
            ind: vec![ind.clone()],
        }))
    }

    fn print_premises(premises: &[Arc<Expr>]) {
        for (i, prem) in premises.iter().enumerate() {
            println!("{i}. {prem}");
        }
    }
}
