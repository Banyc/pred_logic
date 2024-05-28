use std::{collections::HashSet, sync::Arc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Quant(Quant),
    Pred(Pred),
    BinOp(BinOpExpr),
    UnOp(UnOpExpr),
    Ident(Ident),
    Var(Var),
}
impl Expr {
    pub fn is_branching(&self) -> bool {
        match self {
            Expr::BinOp(_) => true,
            Expr::Pred(_) | Expr::Ident(_) | Expr::Var(_) | Expr::UnOp(_) | Expr::Quant(_) => false,
        }
    }

    pub fn add_necessary_paren(&self) -> String {
        if self.is_branching() {
            format!("({})", self)
        } else {
            self.to_string()
        }
    }

    pub fn free_variables(&self) -> HashSet<Var> {
        match self {
            Expr::Quant(x) => {
                let mut var = x.expr.free_variables();
                var.remove(&x.var);
                var
            }
            Expr::Pred(x) => {
                let mut variables = HashSet::new();
                for ind in &x.ind {
                    let var = match ind {
                        Ind::Const(x) => x,
                        Ind::Var(x) => x,
                    };
                    variables.insert(var.clone());
                }
                variables
            }
            Expr::BinOp(x) => {
                let mut left = x.left.free_variables();
                let right = x.right.free_variables();
                left.extend(right);
                left
            }
            Expr::UnOp(x) => x.expr.free_variables(),
            Expr::Ident(_) | Expr::Var(_) => HashSet::new(),
        }
    }
}
impl core::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Quant(x) => write!(f, "{x}"),
            Expr::Pred(x) => write!(f, "{x}"),
            Expr::BinOp(x) => write!(f, "{x}"),
            Expr::UnOp(x) => write!(f, "{x}"),
            Expr::Ident(x) => write!(f, "{x}"),
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
        write!(f, "{}{}", self.name, stacked_ind)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    id: usize,
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
        let left = self.left.add_necessary_paren();
        let right = self.right.add_necessary_paren();
        let op = &self.op;
        write!(f, "{left} {op} {right}")
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
        let expr = self.expr.add_necessary_paren();
        let op = &self.op;
        write!(f, "{op}{expr}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Not,
}
impl core::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "∼"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Quant {
    pub op: QuantOp,
    pub var: Var,
    pub expr: Arc<Expr>,
}
impl Quant {
    pub fn ind(&self) -> Ind {
        Ind::Var(self.var.clone())
    }
}
impl core::fmt::Display for Quant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}{}){}",
            self.op,
            self.var,
            self.expr.add_necessary_paren()
        )
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
pub struct Ident {
    pub left: Ind,
    pub right: Ind,
}
impl core::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.left, self.right)
    }
}
