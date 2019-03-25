use std::collections::HashMap;

use failure_derive::Fail;
use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

use crate::syntax::Id;
use crate::syntax_light::{
    Statement as LightStatement,
    _Statement as _LightStatement,
    Expression as LightExpression,
    _Expression as _LightExpression,
};
use crate::util::SrcLocation;

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
    fn with_toplevel<I: Iterator<Item = String>>(ids: &mut I) -> Stack {
        let mut s = Stack::new();
        s.push_env();

        for id in ids {
            s.add_binding(&id, false);
        }

        return s;
    }

    // Call this whenever we encounter a function literal.
    fn push_env(&mut self) {
        self.0.push((vec![], 0));
        self.push_scope();
    }

    // Call this whenever a new scope is created, except for function literals (use push_env there,
    // which automatically adds an initial scope for the new environment).
    fn push_scope(&mut self) {
        let num_envs = self.0.len();
        self.0[num_envs - 1].0.push(HashMap::new());
    }

    // Call this whenever a scope is closed, including function literals.
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
                match self.0[env_level].0[scope_level].get(id.0.fragment.0) {
                    Some((binding_id, mutability)) => {
                        if mutating && !mutability {
                            return Err(AnalysisError::Immutable(SrcLocation::from_span(&id.0)));
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
        return Err(AnalysisError::Free(SrcLocation::from_span(&id.0)));
    }
}

///////////////////////////////////////////////////////////////////////////////////////
// Yet another syntax tree, this time with DeBruijn indices rather than identifiers. //
///////////////////////////////////////////////////////////////////////////////////////

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<'a>(pub Span<'a>, pub _Expression<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression<'a> {
    Nil,
    Bool(bool),
    Id(DeBruijn),
    If(Box<Expression<'a>>, Vec<Statement<'a>>, Vec<Statement<'a>>),
    While(Box<Expression<'a>>, Vec<Statement<'a>>),
    Try(Vec<Statement<'a>>, Vec<Statement<'a>>, Vec<Statement<'a>>),
    Thrown,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<'a>(pub Span<'a>, pub _Statement<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement<'a> {
    Expression(Expression<'a>),
    Return(Expression<'a>),
    Break(Expression<'a>),
    Throw(Expression<'a>),
    Assign(DeBruijn, Expression<'a>),
}

pub fn analyze_statements<'a, I>(ast: Vec<LightStatement<'a>>, top_level: &mut I) -> Result<Vec<Statement<'a>>, AnalysisError> where
    I: Iterator<Item = String> {
    let mut s = Stack::with_toplevel(top_level);
    let ret = do_analyze_statements(ast, &mut s);
    debug_assert!(s.0.len() == 1, "Mismatched number of push and pops: Too few pops");
    return ret;
}

fn do_analyze_statements<'a>(stmts: Vec<LightStatement<'a>>, s: &mut Stack) -> Result<Vec<Statement<'a>>, AnalysisError> {
    s.push_scope();

    let mut ret = Vec::with_capacity(stmts.len());
    for stmt in stmts.into_iter() {
        ret.push(do_analyze_statement(stmt, s)?);
    }

    s.pop();
    return Ok(ret);
}

fn do_analyze_statement<'a>(stmt: LightStatement<'a>, s: &mut Stack) -> Result<Statement<'a>, AnalysisError> {
    match stmt.1 {
        _LightStatement::Expression(exp) => Ok(Statement(
            stmt.0, _Statement::Expression(do_analyze_exp(exp, s)?)
        )),
        _LightStatement::Return(exp) => Ok(Statement(
            stmt.0, _Statement::Return(do_analyze_exp(exp, s)?)
        )),
        _LightStatement::Break(exp) => Ok(Statement(
            stmt.0, _Statement::Break(do_analyze_exp(exp, s)?)
        )),
        _LightStatement::Throw(exp) => Ok(Statement(
            stmt.0, _Statement::Throw(do_analyze_exp(exp, s)?)
        )),
        _LightStatement::Let { id, mutable, rhs } => {
            let binding_id = s.add_binding(id.0.fragment.0, mutable);
            Ok(Statement(stmt.0, _Statement::Assign(DeBruijn { up: 0, id: binding_id}, do_analyze_exp(rhs, s)?)))
        },
        _LightStatement::Assign(id, rhs) => {
            let binding_id = s.resolve_binding(&id, true)?;
            Ok(Statement(stmt.0, _Statement::Assign(binding_id, do_analyze_exp(rhs, s)?)))
        },
    }
}

fn do_analyze_exp<'a>(exp: LightExpression<'a>, s: &mut Stack) -> Result<Expression<'a>, AnalysisError> {
    match exp.1 {
        _LightExpression::Nil => Ok(Expression(exp.0, _Expression::Nil)),
        _LightExpression::Bool(b) => Ok(Expression(exp.0, _Expression::Bool(b))),
        _LightExpression::Id(id) => {
            Ok(Expression(exp.0, _Expression::Id(s.resolve_binding(&id, false)?)))
        }
        _LightExpression::If(cond, then_block, else_block) => {
            Ok(Expression(exp.0, _Expression::If(
                do_analyze_exp_box(cond, s)?,
                do_analyze_statements(then_block, s)?,
                do_analyze_statements(else_block, s)?
            )))
        }
        _LightExpression::While(cond, body) => {
            Ok(Expression(exp.0, _Expression::While(
                do_analyze_exp_box(cond, s)?,
                do_analyze_statements(body, s)?
            )))
        }
        _LightExpression::Try(try_block, caught_block, finally_block) => {
            let ret_try_block = do_analyze_statements(try_block, s)?;
            Ok(Expression(exp.0, _Expression::Try(
                ret_try_block,
                do_analyze_statements(caught_block, s)?,
                do_analyze_statements(finally_block, s)?
            )))
        }
        _LightExpression::Thrown => Ok(Expression(exp.0, _Expression::Thrown)),
    }
}

fn do_analyze_exp_box<'a>(exp: Box<LightExpression<'a>>, s: &mut Stack) -> Result<Box<Expression<'a>>, AnalysisError> {
    Ok(Box::new(do_analyze_exp(*exp, s)?))
}

// If(Box<Expression<'a>>, Vec<Statement<'a>>, Vec<Statement<'a>>),
// While(Box<Expression<'a>>, Vec<Statement<'a>>),
