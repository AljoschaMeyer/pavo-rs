use std::collections::{HashMap, HashSet};

use failure_derive::Fail;

use crate::syntax::{
    Id,
    Pattern as LightPattern, _Pattern as _LightPattern,
    ArrayPatternOptionals as LightArrayPatternOptionals,
    ArrayPattern as LightArrayPattern
};
use crate::syntax_light::{
    Statement as LightStatement,
    _Statement as _LightStatement,
    Expression as LightExpression,
    _Expression as _LightExpression,
    Patterns as LightPatterns,
};
use crate::util::{SrcLocation, FnWrap as W};
use crate::value::Value;
use crate::context::{Context, PavoResult};

///////////////////////////////////////////////////////////////////////////////////////
// Yet another syntax tree, this time with DeBruijn indices rather than identifiers. //
///////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expression(pub SrcLocation, pub _Expression);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum _Expression {
    Nil,
    Bool(bool),
    Int(i64),
    Id(DeBruijn),
    Try(Vec<Statement>, Patterns, Vec<Statement>, Option<Vec<Statement>>),
    Invocation(Box<Expression>, Vec<Expression>, bool), // bool: true iff in tail position
    Fun(ArrayPattern, Vec<Statement>),
    Case(Box<Expression>, Vec<(Patterns, Vec<Statement>)>),
    Loop(Box<Expression>, Vec<(Patterns, Vec<Statement>)>),
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
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Statement(pub SrcLocation, pub _Statement);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum _Statement {
    Expression(Expression),
    Return(Expression),
    Break(Expression),
    Throw(Expression),
    Assign(Patterns, Expression),
    Rec(Vec<(DeBruijn, ArrayPattern, Vec<Statement>)>)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Patterns(pub SrcLocation, pub Vec<Pattern>, pub Option<Box<Expression>>);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pattern(pub SrcLocation, pub _Pattern);

impl Pattern {
    pub fn array(ap: ArrayPattern) -> Pattern {
        Pattern(SrcLocation::default(), _Pattern::Array(ap))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum _Pattern {
    Blank,
    Id(DeBruijn),
    Nil,
    Bool(bool),
    Int(i64),
    Array(ArrayPattern),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ArrayPattern(pub Vec<Pattern>, pub ArrayPatternOptionals, pub Vec<Pattern>);

impl ArrayPattern {
    pub fn empty() -> ArrayPattern {
        ArrayPattern(vec![], ArrayPatternOptionals::Left(vec![], None) , vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayPatternOptionals {
    Left(Vec<Pattern>, Option<Option<DeBruijn>>),
    Right(Option<Option<DeBruijn>>, Vec<Pattern>),
}

/// Everything that can go wrong in the static analysis.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Fail)]
pub enum AnalysisError {
    #[fail(display = "encountered a free identifier")]
    Free(SrcLocation),
    #[fail(display = "tried to assign to an immutable binding")]
    Immutable(SrcLocation),
    #[fail(display = "encountered a duplicate identifier in a single pattern")]
    PatternDuplicate(Id),
    #[fail(display = "a binding is missing in one of the variants of a pattern (or it might be mutable in some and immutable in other variants)")]
    PatternMissing(SrcLocation),
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
    Ok(Statement(stmt.0, match stmt.1 {
        _LightStatement::Expression(exp) =>  _Statement::Expression(analyze_exp(exp, s, tail)?),
        _LightStatement::Return(exp) => _Statement::Return(analyze_exp(exp, s, true)?),
        _LightStatement::Break(exp) => _Statement::Break(analyze_exp(exp, s, tail)?),
        _LightStatement::Throw(exp) => _Statement::Throw(analyze_exp(exp, s, false)?),
        _LightStatement::Let(pats, rhs) => _Statement::Assign(
            analyze_patterns(pats, s)?,
            analyze_exp(rhs, s, tail)?,
        ),
        _LightStatement::Assign(id, rhs) => {
            let binding_id = s.resolve_binding(&id, true)?;
            _Statement::Assign(
                Patterns(id.1, vec![Pattern(id.1, _Pattern::Id(binding_id))], None),
                analyze_exp(rhs, s, tail)?,
            )
        },
        _LightStatement::Rec(defs) => {
            s.push_scope();

            let de_bruijns: Vec<_> = defs.iter()
                .map(|(id, _, _)| DeBruijn { up: 0, id: s.add_binding(&id.0, false)} )
                .collect();

            let mut analyzed = Vec::with_capacity(defs.len());
            for (i, (_, args, body)) in defs.into_iter().enumerate() {
                s.push_env();
                analyzed.push((
                    de_bruijns[i],
                    analyze_array_pattern(args, s)?,
                    do_analyze_statements(body, s, true)?
                ));
            }

            s.pop();
            _Statement::Rec(analyzed)
        }
    }))
}

fn analyze_exp(exp: LightExpression, s: &mut Stack, tail: bool) -> Result<Expression, AnalysisError> {
    Ok(Expression(exp.0, match exp.1 {
        _LightExpression::Nil => _Expression::Nil,
        _LightExpression::Bool(b) => _Expression::Bool(b),
        _LightExpression::Int(n) => _Expression::Int(n),
        _LightExpression::Id(id) =>  _Expression::Id(s.resolve_binding(&id, false)?),
        _LightExpression::Case(matcher, arms) => {
            let analyzed_matcher = analyze_exp_box(matcher, s, false)?;

            let mut analyzed_arms = Vec::with_capacity(arms.len());
            for (pats, body) in arms.into_iter() {
                s.push_scope();
                analyzed_arms.push((
                    analyze_patterns(pats, s)?,
                    do_analyze_statements(body, s, tail)?
                ));
                s.pop();
            }

            _Expression::Case(analyzed_matcher, analyzed_arms)
        }
        _LightExpression::Loop(matcher, arms) => {
            let analyzed_matcher = analyze_exp_box(matcher, s, false)?;

            let mut analyzed_arms = Vec::with_capacity(arms.len());
            for (pats, body) in arms.into_iter() {
                s.push_scope();
                analyzed_arms.push((
                    analyze_patterns(pats, s)?,
                    do_analyze_statements(body, s, tail)?
                ));
                s.pop();
            }

            _Expression::Loop(analyzed_matcher, analyzed_arms)
        }
        _LightExpression::Try(try_block, pats, caught_block, finally_block) => {
            let analyzed_try_block = do_analyze_statements(try_block, s, tail && finally_block.is_none())?;

            s.push_scope();
            let analyzed_pats = analyze_patterns(pats, s)?;
            let analyzed_caught_block = do_analyze_statements(caught_block, s, tail && finally_block.is_none())?;
            s.pop();

            let analyzed_finally_block = match finally_block {
                Some(block) => Some(do_analyze_statements(block, s, tail)?),
                None => None,
            };

            _Expression::Try(
                analyzed_try_block,
                analyzed_pats,
                analyzed_caught_block,
                analyzed_finally_block,
            )
        }
        _LightExpression::Invocation(fun, args) => _Expression::Invocation(
                analyze_exp_box(fun, s, false)?,
                analyze_exps(args, s, false)?,
                tail
            ),
        _LightExpression::Fun(args, body) => {
            s.push_env();
            _Expression::Fun(
                analyze_array_pattern(args, s)?,
                do_analyze_statements(body, s, true)?,
            )
        }
        _LightExpression::Builtin1(fun, arg) => _Expression::Builtin1(
                fun,
                analyze_exp_box(arg, s, false)?
            ),
        _LightExpression::Builtin2(fun, lhs, rhs) => _Expression::Builtin2(
                fun,
                analyze_exp_box(lhs, s, false)?,
                analyze_exp_box(rhs, s, false)?
            ),
        _LightExpression::BuiltinMany(fun, args) => _Expression::BuiltinMany(
                fun,
                analyze_exps(args, s, false)?
            ),
    }))
}

fn analyze_exp_box(exp: Box<LightExpression>, s: &mut Stack, tail: bool) -> Result<Box<Expression>, AnalysisError> {
    Ok(Box::new(analyze_exp(*exp, s, tail)?))
}

fn analyze_exps(exps: Vec<LightExpression>, s: &mut Stack, tail: bool) -> Result<Vec<Expression>, AnalysisError> {
    let len = exps.len();
    let mut ret = Vec::with_capacity(len);

    for (i, exp) in exps.into_iter().enumerate() {
        ret.push(analyze_exp(exp, s, tail && (i + 1 == len))?);
    }

    return Ok(ret);
}

fn analyze_patterns(pats: LightPatterns, s: &mut Stack) -> Result<Patterns, AnalysisError> {
    let mut all_names = Vec::with_capacity(pats.1.len());
    for inner in pats.1.iter() {
        all_names.push(get_names(inner)?);
    }

    let names = &all_names[0];
    if !all_names.iter().all(|names_i| names_i == names) {
        return Err(AnalysisError::PatternMissing(pats.0));
    }

    let mut bindings = HashMap::new();
    for (id, mutable) in names {
        bindings.insert(id.clone(), s.add_binding(&id, *mutable));
    }

    let inners = pats.1.into_iter().map(|pat| analyze_pattern(pat, &bindings)).collect();

    let guard = match pats.2 {
        Some(exp) => Some(Box::new(analyze_exp(*exp, s, false)?)),
        None => None,
    };

    Ok(Patterns(pats.0, inners, guard))
}

fn analyze_pattern(pat: LightPattern, bindings: &HashMap<String, BindingId>) -> Pattern {
    Pattern(pat.0, match pat.1 {
        _LightPattern::Blank => _Pattern::Blank,
        _LightPattern::Id(id, _) => _Pattern::Id(DeBruijn { up: 0, id: *bindings.get(&id.0).unwrap() }),
        _LightPattern::Nil => _Pattern::Nil,
        _LightPattern::Bool(b) => _Pattern::Bool(b),
        _LightPattern::Int(n) => _Pattern::Int(n),
        _LightPattern::Array(LightArrayPattern(left, opts, right)) => {
            _Pattern::Array(ArrayPattern(
                left.into_iter().map(|p| analyze_pattern(p, bindings)).collect(),
                analyze_pattern_array_optionals(opts, bindings),
                right.into_iter().map(|p| analyze_pattern(p, bindings)).collect(),
            ))
        }
    })
}

fn analyze_pattern_array_optionals(p: LightArrayPatternOptionals, bindings: &HashMap<String, BindingId>) -> ArrayPatternOptionals {
    match p {
        LightArrayPatternOptionals::Left(opts, spread) => ArrayPatternOptionals::Left(
            opts.into_iter().map(|opt| analyze_pattern(opt, bindings)).collect(),
            spread.map(|tmp| tmp.map(|(id, _)| DeBruijn { up: 0, id: *bindings.get(&id.0).unwrap() })),
        ),
        LightArrayPatternOptionals::Right(spread, opts) => ArrayPatternOptionals::Right(
            spread.map(|tmp| tmp.map(|(id, _)| DeBruijn { up: 0, id: *bindings.get(&id.0).unwrap() })),
            opts.into_iter().map(|opt| analyze_pattern(opt, bindings)).collect(),
        ),
    }
}

fn analyze_array_pattern(pat: LightArrayPattern, s: &mut Stack) -> Result<ArrayPattern, AnalysisError> {
    let patterns = LightPatterns(
            SrcLocation::default(),
            vec![LightPattern::arr(pat)],
            None
        );
    let analyzed = analyze_patterns(patterns, s)?;

    for p in analyzed.1.into_iter() { // contains exactly one element, the converted array pattern
        match p.1 {
            _Pattern::Array(arr) => return Ok(arr),
            _ => unreachable!(),
        }
    }
    unreachable!()
}

// Return the set of all (free) names (and their mutabilities) that occur in this pattern.
// Errors if a name occurs more than once (even with different mutabilities).
fn get_names(p: &LightPattern) -> Result<HashSet<(String, bool)>, AnalysisError> {
    let mut n = HashSet::new();
    names_pattern(p, &mut n)?;
    Ok(n)
}

fn names_pattern(p: &LightPattern, n: &mut HashSet<(String, bool)>) -> Result<(), AnalysisError> {
    match &p.1 {
        _LightPattern::Blank | _LightPattern::Nil
        | _LightPattern::Bool(..) | _LightPattern::Int(..) => {}
        _LightPattern::Id(id, mutable) => add_name(id, *mutable, n)?,
        _LightPattern::Array(LightArrayPattern(left, optionals, right)) => {
            for pat in left {
                let _ = names_pattern(pat, n)?;
            }
            for pat in right {
                let _ = names_pattern(pat, n)?;
            }
            match optionals {
                LightArrayPatternOptionals::Left(opts, spread)
                | LightArrayPatternOptionals::Right(spread, opts) => {
                    for pat in opts {
                        let _ = names_pattern(pat, n)?;
                    }

                    if let Some(Some((id, mutable))) = spread {
                        add_name(id, *mutable, n)?;
                    }
                }
            }
        }
    };
    Ok(())
}

fn add_name(id: &Id, mutable: bool, n: &mut HashSet<(String, bool)>) -> Result<(), AnalysisError> {
    if !n.insert((id.0.clone(), mutable)) {
        Err(AnalysisError::PatternDuplicate(id.clone()))
    } else if n.contains(&(id.0.clone(), !mutable)) {
        Err(AnalysisError::PatternDuplicate(id.clone()))
    } else {
        Ok(())
    }
}
