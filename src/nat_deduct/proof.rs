use std::{borrow::Cow, collections::HashSet, sync::Arc};

use crate::{
    constructors::{and, if_p_q, not},
    expr::{BinOp, BinOpExpr, Expr, Ind, UnnamedGen, Var},
    subst::{extract_expr, replace_expr},
};

use super::{
    r#impl::{
        addition, existential_generalization, existential_instantiation, identity_reflexivity,
        simplification, universal_generalization, universal_instantiation, Syllogism,
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
        let premises = premises
            .into_iter()
            .map(|prem| Premise {
                expr: prem,
                ty: PremiseType::Deducted,
            })
            .collect();
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
        self.deduction()
            .premises()
            .iter()
            .any(|prem| prem.expr == self.conclusion)
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
        let prem = Premise {
            expr: Arc::clone(&assume),
            ty: PremiseType::Assumed,
        };
        deduction.push_premise(prem, None);
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
        let cond = if_p_q(Arc::clone(&self.assume), Arc::clone(&last.expr));
        let unnamed_space = self.deduction.unnamed_space().clone();
        let prem = Premise {
            expr: cond,
            ty: PremiseType::Deducted,
        };
        self.prev_proof
            .deduction_mut()
            .push_premise(prem, Some(unnamed_space));
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
        let prem = Premise {
            expr: Arc::clone(&assume),
            ty: PremiseType::Assumed,
        };
        deduction.push_premise(prem, None);
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
        if !contradiction(&last.expr, unnamed_space) {
            return Err(self);
        }
        let prem = Premise {
            expr: not(self.assume),
            ty: PremiseType::Deducted,
        };
        self.prev_proof.deduction_mut().push_premise(prem, None);
        Ok(*self.prev_proof)
    }
}

/// ```math
/// p ⋅ ∼p
/// ```
pub fn contradiction(expr: &Arc<Expr>, mut unnamed_space: UnnamedGen) -> bool {
    let p = Var::Unnamed(unnamed_space.gen());
    let p_expr = Arc::new(Expr::Prop(p.clone()));
    let contradiction = and(Arc::clone(&p_expr), not(p_expr));
    extract_expr(expr, &contradiction).is_some()
}

#[derive(Debug, Clone)]
pub struct SemanticArgument {
    conclusion: Option<Proof>,
    open_proofs: Vec<IndirectProof>,
}
impl SemanticArgument {
    pub fn new(indirect_proof: IndirectProof) -> Self {
        Self {
            conclusion: None,
            open_proofs: vec![indirect_proof],
        }
    }

    pub fn conclude(self) -> Result<Proof, Self> {
        if !self.open_proofs.is_empty() {
            return Err(self);
        }
        Ok(self.conclusion.unwrap())
    }

    pub fn close_last(&mut self) {
        let Some(open_proof) = self.open_proofs.pop() else {
            return;
        };
        let closed_proof = open_proof.conclude();
        match closed_proof {
            Ok(x) => self.conclusion = Some(x),
            Err(x) => self.open_proofs.push(x),
        }
    }

    pub fn last_open_mut(&mut self) -> Option<&mut IndirectProof> {
        self.open_proofs.last_mut()
    }

    pub fn split_last(&mut self) {
        let Some(mut open_proof) = self.open_proofs.last().cloned() else {
            return;
        };
        let prem = open_proof.deduction_mut().pop_premise().unwrap();
        let Expr::BinOp(BinOpExpr {
            op: BinOp::Or,
            left,
            right,
        }) = prem.expr.as_ref()
        else {
            return;
        };
        let left = Premise {
            expr: Arc::clone(left),
            ty: PremiseType::Assumed,
        };
        let right = Premise {
            expr: Arc::clone(right),
            ty: PremiseType::Assumed,
        };
        let mut left_proof = open_proof.clone();
        left_proof.deduction_mut().push_premise(left, None);
        let mut right_proof = open_proof.clone();
        right_proof.deduction_mut().push_premise(right, None);
        self.open_proofs.push(right_proof);
        self.open_proofs.push(left_proof);
    }
}

#[derive(Debug, Clone)]
pub struct Premise {
    pub expr: Arc<Expr>,
    pub ty: PremiseType,
}

#[derive(Debug, Clone)]
pub enum PremiseType {
    Assumed,
    Deducted,
}

#[derive(Debug, Clone)]
pub struct Deduction {
    unnamed_space: UnnamedGen,
    premises: Vec<Premise>,
    free_variables_in_existential_instantiation: HashSet<Var>,
}
impl Deduction {
    pub fn new(premises: Vec<Premise>, unnamed_space: UnnamedGen) -> Self {
        Self {
            unnamed_space,
            premises,
            free_variables_in_existential_instantiation: HashSet::new(),
        }
    }

    pub fn premises(&self) -> &Vec<Premise> {
        &self.premises
    }
    pub fn unnamed_space(&self) -> &UnnamedGen {
        &self.unnamed_space
    }
    pub fn push_premise(&mut self, prem: Premise, unnamed_space: Option<UnnamedGen>) {
        self.premises.push(prem);
        if let Some(x) = unnamed_space {
            self.unnamed_space = x;
        }
    }
    pub fn pop_premise(&mut self) -> Option<Premise> {
        self.premises.pop()
    }

    pub fn syllogism(&mut self, major_prem: usize, minor_prem: usize) {
        let major_prem = &self.premises[major_prem].expr;
        let minor_prem = &self.premises[minor_prem].expr;
        let syllogism = Syllogism {
            major_prem,
            minor_prem,
        };
        let new = syllogism.any(self.unnamed_space.clone());
        self.premises.push(Premise {
            expr: new,
            ty: PremiseType::Deducted,
        });
    }

    pub fn addition(&mut self, prem: usize, new: Arc<Expr>) {
        let prem = &self.premises[prem].expr;
        let Some(expr) = addition(prem, new) else {
            return;
        };
        self.premises.push(Premise {
            expr,
            ty: PremiseType::Deducted,
        });
    }

    pub fn simplification(&mut self, prem: usize) {
        let prem = &self.premises[prem].expr;
        let Some(expr) = simplification(prem) else {
            return;
        };
        self.premises.push(Premise {
            expr,
            ty: PremiseType::Deducted,
        });
    }

    pub fn identity_reflexivity(&mut self, ind: Ind) {
        let expr = identity_reflexivity(ind);
        self.premises.push(Premise {
            expr,
            ty: PremiseType::Deducted,
        })
    }

    pub fn replace(&mut self, prem: usize, patt: impl Fn(Var) -> Arc<Expr>, op: ReplacementOp) {
        let mut unnamed_space = self.unnamed_space.clone();
        let var = Var::Unnamed(unnamed_space.gen());
        let patt = patt(var.clone());

        let prem = &self.premises[prem].expr;
        let Some(mut captured) = extract_expr(prem, &patt) else {
            return;
        };
        // println!("{patt}");
        // println!("{captured:#?}");
        let Some(expr) = captured.expr().get(&var) else {
            return;
        };
        let Some(equiv) = repl::replace(expr, op, self.unnamed_space.clone()) else {
            return;
        };
        captured.force_insert_expr(var, equiv);
        let new = replace_expr(&patt, Cow::Borrowed(&captured));
        self.premises.push(Premise {
            expr: new,
            ty: PremiseType::Deducted,
        });
    }

    pub fn universal_instantiation(&mut self, prem: usize, ind: Ind) {
        let prem = &self.premises[prem].expr;
        let Some(prem) = universal_instantiation(prem, ind) else {
            return;
        };
        self.premises.push(Premise {
            expr: prem,
            ty: PremiseType::Deducted,
        });
    }
    pub fn universal_generalization(&mut self, prem: usize, old: Var, new: Var) {
        let prem = &self.premises[prem];
        if let PremiseType::Assumed = prem.ty {
            return;
        }
        if self
            .free_variables_in_existential_instantiation
            .contains(&old)
        {
            return;
        }
        let Some(prem) = universal_generalization(&prem.expr, old, new) else {
            return;
        };
        self.premises.push(Premise {
            expr: prem,
            ty: PremiseType::Deducted,
        });
    }
    pub fn existential_instantiation(&mut self, prem: usize) -> Option<Var> {
        let prem = &self.premises[prem].expr;
        let (prem, var) = existential_instantiation(prem, &mut self.unnamed_space)?;
        self.free_variables_in_existential_instantiation
            .extend(prem.free_variables());
        self.premises.push(Premise {
            expr: prem,
            ty: PremiseType::Deducted,
        });
        Some(var)
    }
    pub fn existential_generalization(&mut self, prem: usize, old: Ind, new: Var) {
        let prem = &self.premises[prem].expr;
        let Some(prem) = existential_generalization(prem, old, new) else {
            return;
        };
        self.premises.push(Premise {
            expr: prem,
            ty: PremiseType::Deducted,
        });
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        constructors::{
            every, exists, ident, if_p_q, or,
            tests::{named_var_expr, var_expr},
        },
        expr::{Named, Pred},
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

    #[test]
    fn test_ident_reflexivity() {
        let x = named_var("x");
        let i = named_var("i");
        let x_ind = Ind::Var(x.clone());
        let i_ind = Ind::Var(i.clone());
        let b_x = singular_pred("B", x_ind.clone());
        let b_i = singular_pred("B", i_ind.clone());
        let premises = [every(
            x.clone(),
            if_p_q(b_x.clone(), not(ident(x_ind.clone(), i_ind.clone()))),
        )]
        .into();
        let conclusion = not(b_i.clone());
        let mut proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(0, i_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().identity_reflexivity(i_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(2, var_expr, ReplacementOp::DoubleNegation);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(1, 3);
        print_premises(proof.deduction().premises());
        println!();
        assert!(proof.conclude());
    }

    #[test]
    fn test_ident_com_transitivity() {
        let x = named_var("x");
        let s = named_var("s");
        let c = named_var("c");
        let x_ind = Ind::Var(x.clone());
        let s_ind = Ind::Const(s.clone());
        let c_ind = Ind::Const(c.clone());
        let p_s = singular_pred("P", s_ind.clone());
        let i_s = singular_pred("I", s_ind.clone());
        let p_c = singular_pred("P", c_ind.clone());
        let l_c = singular_pred("L", c_ind.clone());
        let p_x = singular_pred("P", x_ind.clone());
        let i_x = singular_pred("I", x_ind.clone());
        let l_x = singular_pred("L", x_ind.clone());
        let premises = [
            and(
                and(p_s.clone(), i_s.clone()),
                every(
                    x.clone(),
                    if_p_q(
                        and(p_x.clone(), i_x.clone()),
                        ident(x_ind.clone(), s_ind.clone()),
                    ),
                ),
            ),
            and(p_c.clone(), l_c.clone()),
            exists(
                x.clone(),
                and(and(p_x.clone(), i_x.clone()), not(l_x.clone())),
            ),
        ]
        .into();
        let conclusion = not(ident(c_ind.clone(), s_ind.clone()));
        let proof = RootProof::new(premises, conclusion);
        print_premises(proof.deduction().premises());
        println!("// {}", proof.conclusion());
        println!();
        let mut proof = IndirectProof::new(
            Box::new(Proof::Root(proof)),
            ident(c_ind.clone(), s_ind.clone()),
        );
        print_premises(proof.deduction().premises());
        println!();
        let a = proof.deduction_mut().existential_instantiation(2).unwrap();
        let a_ind = Ind::Const(a.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(0, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(5);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .universal_instantiation(6, a_ind.clone());
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(4);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(7, 8);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(3, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(9, 10);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(4, 11);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(12, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(13);
        print_premises(proof.deduction().premises());
        println!();
        proof
            .deduction_mut()
            .replace(1, var_expr, ReplacementOp::Commutativity);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().simplification(15);
        print_premises(proof.deduction().premises());
        println!();
        proof.deduction_mut().syllogism(16, 14);
        print_premises(proof.deduction().premises());
        println!();
        let proof = proof.conclude().unwrap().root().unwrap().clone();
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

    fn print_premises(premises: &[Premise]) {
        for (i, prem) in premises.iter().enumerate() {
            let prem = &prem.expr;
            println!("{i}. {prem}");
        }
    }
}
