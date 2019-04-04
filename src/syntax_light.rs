//! Desugared pavo syntax.
//!
//! Regular syntax is translated into this directly after parsing. The remaining layers of the
//! program are only aware of this more manageable pavo subset.

use failure_derive::Fail;

use crate::syntax::{
    Id,
    Statement as PavoStatement,
    _Statement as _PavoStatement,
    Expression as PavoExpression,
    _Expression as _PavoExpression,
    BinOp,
    BinderPatterns,
    BinderPattern,
    _BinderPattern,
    OuterArrayPattern, _OuterArrayPattern,
    ArrayPattern, _ArrayPattern,
};
use crate::builtins;
use crate::util::{FnWrap as W, SrcLocation};
use crate::value::Value;
use crate::context::{Context, PavoResult};

/// Everything that can go wrong when desugaring patterns.
#[derive(PartialEq, Eq, Debug, Clone, Hash, Fail)]
pub enum PatternError {
    #[fail(display = "encountered a duplicate identifier")]
    Duplicate(Id),
    #[fail(display = "a binding is missing in one of the variants of a pattern (or it might be mutable in some and immutable in other variants)")]
    Missing(SrcLocation),
}

impl From<Id> for PatternError {
    fn from(id: Id) -> Self {
        PatternError::Duplicate(id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression(pub SrcLocation, pub _Expression);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression {
    Nil,
    Bool(bool),
    Int(i64),
    Id(Id),
    If(Box<Expression>, Vec<Statement>, Vec<Statement>),
    While(Box<Expression>, Vec<Statement>),
    Try(Vec<Statement>, Vec<Statement>, Vec<Statement>),
    Thrown, // Evaluates to the last value that has been thrown - has no counterpart in real pavo
    Args, // Evaluates to the arguments of a function application as an array - has no counterpart in real pavo
    Invocation(Box<Expression>, Vec<Expression>),
    Fun(Vec<Statement>),
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

#[derive(Debug, Clone, PartialEq)]
pub struct Statement(pub SrcLocation, pub _Statement);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement {
    Expression(Expression),
    Return(Expression),
    Break(Expression),
    Throw(Expression),
    Let {
        id: Id,
        mutable: bool,
        rhs: Expression,
    },
    Assign(Id, Expression),
    Rec(Vec<(Id, Vec<Statement>)>),
}

// Functions for generating ast nodes during desugaring. They have bogus source locations. The
// `&'a str` arguments are an easy way to handle the lifetime requirements, they can be empty.

impl Expression {
    fn nil() -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Nil
        )
    }

    fn bool_(b: bool) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Bool(b)
        )
    }

    fn int_usize(n: usize) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Int(n as i64)
        )
    }

    fn if_(cond: Box<Expression>, then_block: Vec<Statement>, else_block: Vec<Statement>) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::If(cond, then_block, else_block)
        )
    }

    fn id(the_id: Id) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Id(the_id)
        )
    }

    fn thrown() -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Thrown,
        )
    }

    fn args() -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Args,
        )
    }
}

impl Statement {
    fn exp(e: Expression) -> Statement {
        Statement(
            SrcLocation::default(),
            _Statement::Expression(e)
        )
    }

    fn let_(id: Id, mutable: bool, rhs: Expression) -> Statement {
        Statement(
            SrcLocation::default(),
            _Statement::Let { id, mutable, rhs }
        )
    }

    fn throw_(e: Expression) -> Statement {
        Statement(
            SrcLocation::default(),
            _Statement::Throw(e),
        )
    }
}

fn desugar_exp(exp: PavoExpression) -> Result<Expression, PatternError> {
    Ok(Expression(exp.0, match exp.1 {
        _PavoExpression::Nil => _Expression::Nil,
        _PavoExpression::Bool(b) => _Expression::Bool(b),
        _PavoExpression::Int(n) => _Expression::Int(n),
        _PavoExpression::Id(id) => _Expression::Id(id),
        _PavoExpression::If(cond, then_block, else_block) => _Expression::If(
            Box::new(desugar_exp(*cond)?),
            desugar_statements(then_block)?,
            desugar_statements(else_block)?,
        ),
        _PavoExpression::Land(lhs, rhs) => _Expression::If(
            Box::new(desugar_exp(*lhs)?),
            vec![Statement::exp(Expression::if_(
                Box::new(desugar_exp(*rhs)?),
                vec![Statement::exp(Expression::bool_(true))],
                vec![Statement::exp(Expression::bool_(false))]
            ))],
            vec![Statement::exp(Expression::bool_(false))],
        ),
        _PavoExpression::Lor(lhs, rhs) => _Expression::If(
            Box::new(desugar_exp(*lhs)?),
            vec![Statement::exp(Expression::bool_(true))],
            vec![Statement::exp(Expression::if_(
                Box::new(desugar_exp(*rhs)?),
                vec![Statement::exp(Expression::bool_(true))],
                vec![Statement::exp(Expression::bool_(false))]
            ))],
        ),
        _PavoExpression::While(cond, body) => _Expression::While(
            Box::new(desugar_exp(*cond)?),
            desugar_statements(body)?,
        ),
        _PavoExpression::Try(try_block, binder, caught_block, finally_block) => {
            let mut caught_buf = vec![Statement::let_(Id::caught(), false, Expression::thrown())];
            desugar_binder_patterns(binder, &mut caught_buf, true)?;
            do_desugar_statements(caught_block, &mut caught_buf)?;
            _Expression::Try(
                desugar_statements(try_block)?,
                caught_buf,
                desugar_statements(finally_block)?
            )
        },
        _PavoExpression::QM(inner) => desugar_exp(PavoExpression::try_(
            vec![PavoStatement::exp((*inner).into())],
            BinderPatterns::blank(),
            vec![PavoStatement::exp(PavoExpression::nil())],
            vec![]
        ))?.1,
        _PavoExpression::Invocation(fun, args) => {
            let mut desugared_args = Vec::with_capacity(args.len());

            for arg in args.into_iter() {
                desugared_args.push(desugar_exp(arg)?);
            }

            _Expression::Invocation(
                Box::new(desugar_exp(*fun)?),
                desugared_args
            )
        }
        _PavoExpression::Method(first_arg, method_exp, remaining_args) => {
            let mut desugared_args = Vec::with_capacity(1 + remaining_args.len());
            desugared_args.push(desugar_exp(*first_arg)?);

            for arg in remaining_args.into_iter() {
                desugared_args.push(desugar_exp(arg)?);
            }

            _Expression::Invocation(
                Box::new(desugar_exp(*method_exp)?),
                desugared_args
            )
        }
        _PavoExpression::BinOp(lhs, op, rhs) => match op {
            BinOp::Eq => _Expression::Builtin2(
                W(builtins::eq),
                Box::new(desugar_exp(*lhs)?),
                Box::new(desugar_exp(*rhs)?),
            ),
            BinOp::Subtract => _Expression::Builtin2(
                W(builtins::int_bin_minus),
                Box::new(desugar_exp(*lhs)?),
                Box::new(desugar_exp(*rhs)?),
            ),
        }
        _PavoExpression::Array(inners) => {
            let mut desugared = Vec::with_capacity(inners.len());

            for inner in inners.into_iter() {
                desugared.push(desugar_exp(inner)?);
            }

            _Expression::BuiltinMany(
                W(builtins::arr_new),
                desugared
            )
        }
        _PavoExpression::Fun(args, body) => _Expression::Fun(desugar_fun(args, body)?),
    }))
}

fn desugar_fun(args: OuterArrayPattern, body: Vec<PavoStatement>) -> Result<Vec<Statement>, PatternError> {
    let mut stmts = vec![Statement::let_(Id::pat(0), false, Expression::args())];

    do_desugar_binder_outer_array_pattern(args, &mut stmts, Some(0));
    do_desugar_statements(body, &mut stmts)?;

    Ok(stmts)
}

pub fn desugar_statements(stmts: Vec<PavoStatement>) -> Result<Vec<Statement>, PatternError> {
    let mut buf = vec![];
    do_desugar_statements(stmts, &mut buf)?;
    Ok(buf)
}

fn do_desugar_statements(stmts: Vec<PavoStatement>, buf: &mut Vec<Statement>) -> Result<(), PatternError> {
    for stmt in stmts.into_iter() {
        desugar_statement(stmt, buf)?;
    }
    Ok(())
}

fn desugar_statement(stmt: PavoStatement, buf: &mut Vec<Statement>) -> Result<(), PatternError> {
    match stmt.1 {
        _PavoStatement::Expression(exp) => Ok(buf.push(Statement(
            stmt.0, _Statement::Expression(desugar_exp(exp)?)
        ))),
        _PavoStatement::Return(exp) => Ok(buf.push(Statement(
            stmt.0, _Statement::Return(desugar_exp(exp)?)
        ))),
        _PavoStatement::Break(exp) => Ok(buf.push(Statement(
            stmt.0, _Statement::Break(desugar_exp(exp)?)
        ))),
        _PavoStatement::Throw(exp) => Ok(buf.push(Statement(
            stmt.0, _Statement::Throw(desugar_exp(exp)?)
        ))),
        _PavoStatement::Let(pat, rhs) => {
            buf.push(Statement(
                stmt.0,
                _Statement::Let { id: Id::pat(0), mutable: false, rhs: desugar_exp(rhs)? }
            ));
            desugar_binder_patterns(pat, buf, false)
        }
        _PavoStatement::Assign(id, exp) => Ok(buf.push(Statement(
            stmt.0, _Statement::Assign(id, desugar_exp(exp)?)
        ))),
        _PavoStatement::Rec(defs) => {
            let mut desugared = Vec::with_capacity(defs.len());

            for (id, args, body) in defs.into_iter() {
                desugared.push((id, desugar_fun(args, body)?));
            }

            Ok(buf.push(Statement(
                stmt.0,
                _Statement::Rec(desugared)
            )))
        }
    }
}

fn desugar_binder_patterns(pats: BinderPatterns, buf: &mut Vec<Statement>, thrown: bool) -> Result<(), PatternError> {
    if pats.1.len() == 1 {
        let _ = pats.1[0].bindings()?;
        do_desugar_binder_pattern(pats.1[0].clone(), buf, if thrown {None} else {Some(0)});
        if let Some(guard) = pats.2 {
            buf.push(Statement::exp(Expression::if_(
                Box::new(desugar_exp(*guard)?),
                vec![],
                vec![Statement::throw_(Expression::nil())]
            )))
        }
        Ok(())
    } else {
        // Check that all patterns bind the same identifiers (including identical mutability)
        let names_to_bind = pats.1[0].bindings()?;
        for pat in pats.1.iter() {
            if pat.bindings()? != names_to_bind {
                return Err(PatternError::Missing(pat.0));
            }
        }

        // desugar `pat0 | pat1 if guard` (with names_to_bind a and mut b) to
        //  let [a, mut b] = try {
        //    let pat0 = ß0; [a, b]
        //  } catch _ {
        //    try {
        //      let pat1 = ß0; [a, b]
        //    } catch _ {
        //      throw nil
        //    }
        //  }
        //  if guard {} else { throw nil }

        let arr_of_ids = PavoExpression::array(names_to_bind.iter().map(
            |(id, _)| PavoExpression::id(id)
        ).collect());

        let bps = BinderPatterns(pats.0, vec![BinderPattern::arr_from_ids(&names_to_bind)], None);
        let rhs = pats.1.into_iter().rev()
            .map(|pat| vec![
                    PavoStatement(SrcLocation::default(), _PavoStatement::Let(
                        BinderPatterns(SrcLocation::default(), vec![pat], None),
                        PavoExpression(SrcLocation::default(), _PavoExpression::Id(Id::pat(0)))
                    )),
                    PavoStatement::exp(arr_of_ids.clone())
                ])
            .fold(
                vec![PavoStatement::throw_nil()],
                |acc, try_stmts| vec![PavoStatement::exp(PavoExpression::try_(
                    try_stmts,
                    BinderPatterns(SrcLocation::default(), vec![BinderPattern::blank()], None),
                    acc,
                    vec![]
                ))]
            );
        let rhs = match &rhs[0].1 {
            _PavoStatement::Expression(exp) => exp.clone(),
            _ => unreachable!(),
        };

        desugar_statement(PavoStatement(pats.0, _PavoStatement::Let(bps, rhs)), buf)?;
        // add guard if Some
        if let Some(guard) = pats.2 {
            buf.push(Statement::exp(Expression::if_(
                Box::new(desugar_exp(*guard)?),
                vec![],
                vec![Statement::throw_(Expression::nil())]
            )));
        }
        Ok(())
    }
}

fn level_to_id(level: Option<usize>) -> Id {
    match level {
        Some(level) => Id::pat(level),
        None => Id::caught(),
    }
}

fn do_desugar_binder_pattern(pat: BinderPattern, buf: &mut Vec<Statement>, level: Option<usize>) {
    match pat.1 {
        _BinderPattern::Blank => { /* no-op */ },
        _BinderPattern::Id(id, mutable) => {
            buf.push(Statement::let_(id, mutable, Expression::id(level_to_id(level))));
        }
        _BinderPattern::Array(p @ OuterArrayPattern(..)) => do_desugar_binder_outer_array_pattern(p, buf, level),
    }
}

fn do_desugar_binder_array_pattern(pat: ArrayPattern, buf: &mut Vec<Statement>, level: Option<usize>) {
    match pat.1 {
        _ArrayPattern::Regular(inner) => do_desugar_binder_pattern(inner, buf, level),
        _ArrayPattern::QM(id, mutable) => {
            buf.push(Statement::let_(id, mutable, Expression::id(level_to_id(level))));
        }
    }
}

fn do_desugar_binder_outer_array_pattern(OuterArrayPattern(src, p): OuterArrayPattern, buf: &mut Vec<Statement>, level: Option<usize>) {
    buf.push(Statement::exp(Expression(src, _Expression::Builtin1(
        W(builtins::assert_arr),
        Box::new(Expression::id(level_to_id(level)))
    ))));

    let (open, named_remaining) = match p {
        _OuterArrayPattern::Closed(_) => (false, None),
        _OuterArrayPattern::Open(_) => (true, None),
        _OuterArrayPattern::OpenNamed(_, ref id, mutable) => (true, Some((id.clone(), mutable))),
    };

    let num_inners;
    match p {
        _OuterArrayPattern::Closed(inners) |
        _OuterArrayPattern::Open(inners) |
        _OuterArrayPattern::OpenNamed(inners, _, _) => {
            num_inners = inners.len();
            for (i, inner) in inners.into_iter().enumerate() {
                buf.push(Statement(
                    inner.0,
                    _Statement::Let {
                        id: level_to_id(level.map(|lvl| lvl + 1)),
                        mutable: false,
                        rhs: Expression(src, _Expression::Builtin2(
                            if inner.is_regular() {
                                W(builtins::arr_get)
                            } else {
                                W(builtins::arr_get_or_nil)
                            },
                            Box::new(Expression::id(level_to_id(level))),
                            Box::new(Expression::int_usize(i))
                        ))
                    }
                ));
                do_desugar_binder_array_pattern(inner, buf, level.map(|lvl| lvl + 1));
            }

            if !open {
                buf.push(Statement::exp(Expression(src, _Expression::Builtin2(
                    W(builtins::assert_arr_len_at_most),
                    Box::new(Expression::id(level_to_id(level))),
                    Box::new(Expression::int_usize(num_inners))
                ))));
            }

            if let Some((id, mutable)) = named_remaining {
                buf.push(Statement::let_(id.clone(), mutable, Expression(src, _Expression::Builtin2(
                    W(builtins::arr_splice_suffix_helpful),
                    Box::new(Expression::id(level_to_id(level))),
                    Box::new(Expression::int_usize(num_inners))
                ))));
            }
        }
    }
}
