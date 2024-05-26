pub mod r#impl;
pub mod repl;

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::expr::{Expr, Named, Var};

    pub fn named_var_expr(name: &str) -> Arc<Expr> {
        Arc::new(Expr::Var(Var::Named(Named { name: name.into() })))
    }
}
