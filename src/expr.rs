use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Pred(Pred),
    BinOp(BinOpExpr),
    UnOp(UnOpExpr),
    EquivInd(EquivInd),
    Var(Var),
}
impl core::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Pred(x) => write!(f, "{x}"),
            Expr::BinOp(x) => write!(f, "{x}"),
            Expr::UnOp(x) => write!(f, "{x}"),
            Expr::EquivInd(x) => write!(f, "{x}"),
            Expr::Var(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pred {
    pub name: Arc<str>,
    pub ind: Vec<Ind>,
}
impl core::fmt::Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut stacked_ind = String::new();
        for ind in &self.ind {
            stacked_ind.push(' ');
            stacked_ind.push_str(&ind.to_string());
        }
        write!(f, "{} {}", self.name, stacked_ind)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ind {
    Const(Var),
    Var(Var),
}
impl core::fmt::Display for Ind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ind::Const(x) => write!(f, "{x}"),
            Ind::Var(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Var {
    Named(Named),
    Unnamed(Unnamed),
}
impl core::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Named(x) => write!(f, "{x}"),
            Var::Unnamed(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Named {
    pub name: Arc<str>,
}
impl core::fmt::Display for Named {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Unnamed {
    pub id: usize,
}
impl core::fmt::Display for Unnamed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
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
impl core::fmt::Display for BinOpExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}) {} ({})", self.left, self.op, self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    And,
    Or,
    If,
}
impl core::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::And => write!(f, "⋅"),
            BinOp::Or => write!(f, "∨"),
            BinOp::If => write!(f, "⊃"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Arc<Expr>,
}
impl core::fmt::Display for UnOpExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.op, self.expr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Quant(Quant),
}
impl core::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "∼"),
            UnOp::Quant(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Quant {
    pub op: QuantOp,
    pub ind: Ind,
}
impl core::fmt::Display for Quant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}{})", self.op, self.ind)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantOp {
    Every,
    Exists,
}
impl core::fmt::Display for QuantOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantOp::Every => write!(f, ""),
            QuantOp::Exists => write!(f, "∃"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EquivInd {
    pub left: Ind,
    pub right: Ind,
}
impl core::fmt::Display for EquivInd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.left, self.right)
    }
}
