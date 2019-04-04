use std::collections::HashMap;

use failure_derive::Fail;

use crate::syntax::Id;
use crate::syntax_light::{
    Statement as LightStatement,
    _Statement as _LightStatement,
    Expression as LightExpression,
    _Expression as _LightExpression,
};
use crate::util::{SrcLocation, FnWrap as W};
use crate::value::Value;
use crate::context::{Context, PavoResult};

/// Everything that can go wrong in the static analysis.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Fail)]
pub enum AnalysisError {
    #[fail(display = "encountered a free identifier")]
    Free(SrcLocation),
    #[fail(display = "tried to assign to an immutable binding")]
    Immutable(SrcLocation),
}

pub type BindingId = usize;

// Indicates the path from a bound identifier site to its binder.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeBruijn {
    // How many environments we need to go up to find the binder.
    pub up: usize,
    // The numeric id of the binder within its environment.
    pub id: BindingId,
}

// A stack of scopes maintained during binding analysis. The outer vec contains environments
// (function boundaries), the inner vecs contain nested scopes (all other curly braces). Per scope,
// we keep a mapping from identifier strings to a numeric id and mutability for that binding.
// We store the largest BindingId assigned so far per environment (so by the end, we flatten all
// scopes within the same environment into a single numeric id space).
struct Stack(Vec<(Vec<HashMap<String, (BindingId, bool)>>, BindingId)>);

impl Stack {
    // Create a new, empty Stack.
    fn new() -> Stack {
        Stack(vec![])
    }

    // Create a new Stack with a top-level environment containing all the items of the given
    // iterator as immutable binders (with BindingIds assigned in ascending order). This will do
    // unexpected things if the iterator emits some pairwise equal strings (but why would you do
    // that?).
    fn with_toplevel(ids: &'static [&'static str]) -> Stack {
        let mut s = Stack::new();
        s.push_env();
        s.push_scope();

        for id in ids {
            s.add_binding(&id, false);
        }

        s.push_env();

        return s;
    }

    // Call this whenever we encounter a function literal.
    fn push_env(&mut self) {
        self.0.push((vec![], 0));
    }

    // Call this whenever a new scope is created, except for function literals (use push_env there).
    fn push_scope(&mut self) {
        let num_envs = self.0.len();
        self.0[num_envs - 1].0.push(HashMap::new());
    }

    // Call this whenever a scope is closed.
    // This automatically pops an environment once its last scope is popped.
    fn pop(&mut self) {
        let num_envs = self.0.len();
        let scopes = &mut self.0[num_envs - 1].0;
        let num_scopes = scopes.len();

        if num_scopes > 1 {
            scopes.pop();
        } else {
            debug_assert!(
                num_scopes == 1 && num_envs > 0,
                "mismatched pushs and pops, to many pops"
            );
            self.0.pop();
        }
    }

    // Call this whenever a new identifier is bound (let, catch and arguments).
    fn add_binding(&mut self, id: &str, mutable: bool) -> BindingId {
        let num_envs = self.0.len();
        let (scopes, max_id) = &mut self.0[num_envs - 1];
        let num_scopes = scopes.len();

        let map = &mut scopes[num_scopes - 1];
        let new_id = *max_id;
        *max_id += 1;
        map.insert(id.to_string(), (new_id, mutable));
        new_id
    }

    // Call whenever an identifier expression is encountered to find out the corresponding binding.
    // Errors if the identifier is free, or if mutating is `true` but the binding is immutable.
    fn resolve_binding(&self, id: &Id, mutating: bool) -> Result<DeBruijn, AnalysisError> {
        let num_envs = self.0.len();
        let mut env_level = num_envs - 1;

        // traverse all environments in lifo order
        loop {
            let num_scopes = self.0[env_level].0.len();
            let mut scope_level = num_scopes - 1;

            // traverse all scopes in lifo order
            loop  {
                match self.0[env_level].0[scope_level].get(&id.0) {
                    Some((binding_id, mutability)) => {
                        if mutating && !mutability {
                            return Err(AnalysisError::Immutable(id.1));
                        } else {
                            return Ok(DeBruijn {
                                up: num_envs - (env_level + 1),
                                id: *binding_id,
                            });
                        }
                    }
                    None => {}
                }

                if scope_level > 0 {
                    scope_level -= 1;
                } else {
                    break;
                }
            }

            if env_level > 0 {
                env_level -= 1;
            } else {
                break;
            }
        }

        // We looked in all scopes and all environments, but the id wasn't bound.
        return Err(AnalysisError::Free(id.1));
    }
}

///////////////////////////////////////////////////////////////////////////////////////
// Yet another syntax tree, this time with DeBruijn indices rather than identifiers. //
///////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq)]
pub struct Expression(pub SrcLocation, pub _Expression);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression {
    Nil,
    Bool(bool),
    Int(i64),
    Id(DeBruijn),
    If(Box<Expression>, Vec<Statement>, Vec<Statement>),
    While(Box<Expression>, Vec<Statement>),
    Try(Vec<Statement>, Vec<Statement>, Vec<Statement>),
    Fun(Vec<Statement>),
    Invocation(Box<Expression>, Vec<Expression>, bool), // bool: true iff in tail position
    Builtin1(
        W<fn(&Value, &mut Context) -> PavoResult>,
        Box<Expression>
    ),
    Builtin2(
        W<fn(&Value, &Value, &mut Context) -> PavoResult>,
        Box<Expression>,
        Box<Expression>
    ),
    BuiltinMany(
        W<fn(&[Value], &mut Context) -> PavoResult>,
        Vec<Expression>,
    ),
    NoOp,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement(pub SrcLocation, pub _Statement);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement {
    Expression(Expression),
    Return(Expression),
    Break(Expression),
    Throw(Expression),
    Assign(DeBruijn, Expression),
    Rec(Vec<(DeBruijn, Vec<Statement>)>)
}

pub fn analyze_statements(ast: Vec<LightStatement>, top_level: &'static [&'static str]) -> Result<Vec<Statement>, AnalysisError> {
    let mut s = Stack::with_toplevel(top_level);
    let ret = do_analyze_statements(ast, &mut s, true);
    if ret.is_ok() {
        debug_assert!(
            s.0.len() == 1, "Mismatched number of push and pops: Too few pops, stack: {:?}", s.0
        );
    }
    return ret;
}

fn do_analyze_statements(stmts: Vec<LightStatement>, s: &mut Stack, tail: bool) -> Result<Vec<Statement>, AnalysisError> {
    s.push_scope();

    let len = stmts.len();
    let mut ret = Vec::with_capacity(len);
    for (i, stmt) in stmts.into_iter().enumerate() {
        ret.push(do_analyze_statement(stmt, s, tail && (i + 1 == len))?);
    }

    s.pop();
    return Ok(ret);
}

fn do_analyze_statement(stmt: LightStatement, s: &mut Stack, tail: bool) -> Result<Statement, AnalysisError> {
    match stmt.1 {
        _LightStatement::Expression(exp) => Ok(Statement(
            stmt.0, _Statement::Expression(do_analyze_exp(exp, s, tail)?)
        )),
        _LightStatement::Return(exp) => Ok(Statement(
            stmt.0, _Statement::Return(do_analyze_exp(exp, s, true)?)
        )),
        _LightStatement::Break(exp) => Ok(Statement(
            stmt.0, _Statement::Break(do_analyze_exp(exp, s, tail)?)
        )),
        _LightStatement::Throw(exp) => Ok(Statement(
            stmt.0, _Statement::Throw(do_analyze_exp(exp, s, false)?)
        )),
        _LightStatement::Let { id, mutable, rhs } => {
            let rhs = do_analyze_exp(rhs, s, false)?;
            let binding_id = s.add_binding(&id.0, mutable);
            Ok(Statement(stmt.0, _Statement::Assign(DeBruijn { up: 0, id: binding_id}, rhs)))
        },
        _LightStatement::Assign(id, rhs) => {
            let binding_id = s.resolve_binding(&id, true)?;
            Ok(Statement(stmt.0, _Statement::Assign(binding_id, do_analyze_exp(rhs, s, false)?)))
        },
        _LightStatement::Rec(defs) => {
            let mut defs2 = Vec::with_capacity(defs.len());
            let defs1: Vec<_> = defs.into_iter()
                .map(|(id, body)| (DeBruijn { up:0, id: s.add_binding(&id.0, false) }, body))
                .collect();

            for (de_bruijn, body) in defs1.into_iter() {
                s.push_env();
                defs2.push((de_bruijn, do_analyze_statements(body, s, true)?));
            }

            Ok(Statement(stmt.0, _Statement::Rec(defs2)))
        }
    }
}

fn do_analyze_exp(exp: LightExpression, s: &mut Stack, tail: bool) -> Result<Expression, AnalysisError> {
    match exp.1 {
        _LightExpression::Nil => Ok(Expression(exp.0, _Expression::Nil)),
        _LightExpression::Bool(b) => Ok(Expression(exp.0, _Expression::Bool(b))),
        _LightExpression::Int(n) => Ok(Expression(exp.0, _Expression::Int(n))),
        _LightExpression::Id(id) => {
            Ok(Expression(exp.0, _Expression::Id(s.resolve_binding(&id, false)?)))
        }
        _LightExpression::If(cond, then_block, else_block) => {
            Ok(Expression(exp.0, _Expression::If(
                do_analyze_exp_box(cond, s, false)?,
                do_analyze_statements(then_block, s, tail)?,
                do_analyze_statements(else_block, s, tail)?
            )))
        }
        _LightExpression::While(cond, body) => {
            Ok(Expression(exp.0, _Expression::While(
                do_analyze_exp_box(cond, s, false)?,
                do_analyze_statements(body, s, false)?
            )))
        }
        _LightExpression::Try(try_block, caught_block, finally_block) => {
            let ret_try_block = do_analyze_statements(try_block, s, false)?;
            Ok(Expression(exp.0, _Expression::Try(
                ret_try_block,
                do_analyze_statements(caught_block, s, false)?,
                do_analyze_statements(finally_block, s, tail)?
            )))
        }
        _LightExpression::Thrown => Ok(Expression(exp.0, _Expression::NoOp)),
        _LightExpression::Args => Ok(Expression(exp.0, _Expression::NoOp)),
        _LightExpression::Invocation(fun, args) => {
            Ok(Expression(exp.0, _Expression::Invocation(
                do_analyze_exp_box(fun, s, false)?,
                do_analyze_exps(args, s, false)?,
                tail
            )))
        }
        _LightExpression::Fun(body) => {
            s.push_env();
            Ok(Expression(exp.0, _Expression::Fun(
                do_analyze_statements(body, s, true)?,
            )))
        }
        _LightExpression::Builtin1(fun, arg) => {
            Ok(Expression(exp.0, _Expression::Builtin1(
                fun,
                do_analyze_exp_box(arg, s, false)?
            )))
        }
        _LightExpression::Builtin2(fun, lhs, rhs) => {
            Ok(Expression(exp.0, _Expression::Builtin2(
                fun,
                do_analyze_exp_box(lhs, s, false)?,
                do_analyze_exp_box(rhs, s, false)?
            )))
        }
        _LightExpression::BuiltinMany(fun, args) => {
            Ok(Expression(exp.0, _Expression::BuiltinMany(
                fun,
                do_analyze_exps(args, s, false)?
            )))
        }
    }
}

fn do_analyze_exp_box(exp: Box<LightExpression>, s: &mut Stack, tail: bool) -> Result<Box<Expression>, AnalysisError> {
    Ok(Box::new(do_analyze_exp(*exp, s, tail)?))
}

fn do_analyze_exps(exps: Vec<LightExpression>, s: &mut Stack, tail: bool) -> Result<Vec<Expression>, AnalysisError> {
    let len = exps.len();
    let mut ret = Vec::with_capacity(len);

    for (i, exp) in exps.into_iter().enumerate() {
        ret.push(do_analyze_exp(exp, s, tail && (i + 1 == len))?);
    }

    return Ok(ret);
}
