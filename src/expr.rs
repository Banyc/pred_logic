use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Pred(Pred),
    BinOp(BinOpExpr),
    UnOp(UnOpExpr),
    EquivInd(EquivInd),
    Var(Var),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pred {
    pub name: Arc<str>,
    pub ind: Vec<Ind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ind {
    Const(Var),
    Var(Var),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Var {
    Named(Named),
    Unnamed(Unnamed),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Named {
    pub name: Arc<str>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Unnamed {
    pub id: usize,
}

#[derive(Debug, Clone)]
pub struct UnnamedGen {
    next: usize,
}
impl UnnamedGen {
    pub fn new() -> Self {
        Self { next: 0 }
    }

    pub fn gen(&mut self) -> Unnamed {
        let id = self.next;
        self.next += 1;
        Unnamed { id }
    }
}
impl Default for UnnamedGen {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinOpExpr {
    pub op: BinOp,
    pub left: Arc<Expr>,
    pub right: Arc<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    And,
    Or,
    If,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Arc<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Quant(Quant),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Quant {
    pub op: QuantOp,
    pub subject: Ind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantOp {
    Every,
    Exists,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EquivInd {
    pub left: Ind,
    pub right: Ind,
}
