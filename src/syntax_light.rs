//! Desugared pavo syntax.
//!
//! Regular syntax is translated into this directly after parsing. The remaining layers of the
//! program are only aware of this smaller pavo subset.

use crate::syntax::{
    Id,
    Statement as PavoStatement,
    _Statement as _PavoStatement,
    Expression as PavoExpression,
    _Expression as _PavoExpression,
    BinOp,
    Patterns as PavoPatterns,
    Pattern,
    ArrayPattern,
};
use crate::builtins;
use crate::util::{FnWrap as W, SrcLocation};
use crate::value::Value;
use crate::context::{Context, PavoResult};

#[derive(Debug, Clone, PartialEq)]
pub struct Expression(pub SrcLocation, pub _Expression);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression {
    Nil,
    Bool(bool),
    Int(i64),
    Id(Id),
    Try(Vec<Statement>, Patterns, Vec<Statement>, Option<Vec<Statement>>),
    Invocation(Box<Expression>, Vec<Expression>),
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

#[derive(Debug, Clone, PartialEq)]
pub struct Statement(pub SrcLocation, pub _Statement);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement {
    Expression(Expression),
    Return(Expression),
    Break(Expression),
    Throw(Expression),
    Let(Patterns, Expression),
    Assign(Id, Expression),
    Rec(Vec<(Id, ArrayPattern, Vec<Statement>)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Patterns(pub SrcLocation, pub Vec<Pattern>, pub Option<Box<Expression>>);

impl From<Box<PavoExpression>> for Box<Expression> {
    fn from(exp: Box<PavoExpression>) -> Self {
        Box::new((*exp).into())
    }
}

impl From<PavoExpression> for Expression {
    fn from(exp: PavoExpression) -> Expression {
        Expression(exp.0, match exp.1 {
            _PavoExpression::Nil => _Expression::Nil,
            _PavoExpression::Bool(b) => _Expression::Bool(b),
            _PavoExpression::Int(n) => _Expression::Int(n),
            _PavoExpression::Id(id) => _Expression::Id(id),
            _PavoExpression::If(cond, then_block, else_block) => Expression::from(PavoExpression::case(
                cond,
                vec![
                    (
                        // `nil | false => else_block`
                        PavoPatterns::dummy(vec![Pattern::nil(), Pattern::bool_(false)]),
                        else_block.unwrap_or(vec![])
                    ),
                    (
                        // `_ => then_block`
                        PavoPatterns::dummy(vec![Pattern::blank()]),
                        then_block
                    )
                ]
            )).1,
            _PavoExpression::Land(lhs, rhs) => Expression::from(PavoExpression::if_(
                lhs,
                vec![PavoStatement::exp(PavoExpression::if_(
                    rhs,
                    vec![PavoStatement::exp(PavoExpression::bool_(true))],
                    Some(vec![PavoStatement::exp(PavoExpression::bool_(false))]),
                ))],
                Some(vec![PavoStatement::exp(PavoExpression::bool_(false))])
            )).1,
            _PavoExpression::Lor(lhs, rhs) => Expression::from(PavoExpression::if_(
                lhs,
                vec![PavoStatement::exp(PavoExpression::bool_(true))],
                Some(vec![PavoStatement::exp(PavoExpression::if_(
                    rhs,
                    vec![PavoStatement::exp(PavoExpression::bool_(true))],
                    Some(vec![PavoStatement::exp(PavoExpression::bool_(false))]),
                ))])
            )).1,
            _PavoExpression::While(cond, body) => _Expression::Loop(
                Box::new(Expression(
                    SrcLocation::default(),
                    _Expression::Builtin1(W(builtins::truthy), cond.into())
                )),
                vec![(
                        // `true => body`
                        Patterns(SrcLocation::default(), vec![Pattern::bool_(true)], None),
                        desugar_stmts(body),
                    )]
            ),
            _PavoExpression::Case(matcher, arms) => _Expression::Case(
                matcher.into(),
                arms.into_iter().map(|(pats, block)| (pats.into(), desugar_stmts(block))).collect(),
            ),
            _PavoExpression::Loop(matcher, arms) => _Expression::Loop(
                matcher.into(),
                arms.into_iter().map(|(pats, block)| (pats.into(), desugar_stmts(block))).collect(),
            ),
            _PavoExpression::Try(try_block, binder, caught_block, finally_block) => _Expression::Try(
                desugar_stmts(try_block),
                binder.into(),
                desugar_stmts(caught_block),
                finally_block.map(desugar_stmts),
            ),
            _PavoExpression::QM(inner) => Expression::from(PavoExpression::try_(
                vec![PavoStatement::exp(*inner)],
                PavoPatterns::dummy(vec![Pattern::blank()]),
                vec![PavoStatement::exp(PavoExpression::nil())],
                None,
            )).1,
            _PavoExpression::Invocation(fun, args) => _Expression::Invocation(
                fun.into(),
                desugar_exps(args)
            ),
            _PavoExpression::Method(first_arg, method_exp, mut remaining_args) => {
                let mut args = Vec::with_capacity(1 + remaining_args.len());
                args.push(*first_arg);
                args.append(&mut remaining_args);
                Expression::from(PavoExpression::invocation(method_exp, args)).1
            }
            _PavoExpression::BinOp(lhs, op, rhs) => match op {
                BinOp::Eq => _Expression::Builtin2(
                    W(builtins::eq),
                    lhs.into(),
                    rhs.into(),
                ),
                BinOp::Subtract => _Expression::Builtin2(
                    W(builtins::int_bin_minus),
                    lhs.into(),
                    rhs.into(),
                ),
            }
            _PavoExpression::Array(inners) => _Expression::BuiltinMany(
                    W(builtins::arr_new),
                    desugar_exps(inners)
                ),
            _PavoExpression::Fun(args, body) => _Expression::Fun(
                args,
                desugar_stmts(body),
            ),
        })
    }
}

fn desugar_exps(exps: Vec<PavoExpression>) -> Vec<Expression> {
    exps.into_iter().map(Into::into).collect()
}

impl From<PavoStatement> for Statement {
    fn from(stmt: PavoStatement) -> Statement {
        Statement(stmt.0, match stmt.1 {
            _PavoStatement::Expression(exp) => _Statement::Expression(exp.into()),
            _PavoStatement::Return(exp) => _Statement::Return(exp.into()),
            _PavoStatement::Break(exp) => _Statement::Break(exp.into()),
            _PavoStatement::Throw(exp) => _Statement::Throw(exp.into()),
            _PavoStatement::Let(pat, rhs) => _Statement::Let(pat.into(), rhs.into()),
            _PavoStatement::Assign(id, exp) => _Statement::Assign(id, exp.into()),
            _PavoStatement::Rec(defs) => _Statement::Rec(
                defs.into_iter().map(|(id, args, body)| (id, args, desugar_stmts(body))).collect()
            )
        })
    }
}

pub fn desugar_stmts(stmts: Vec<PavoStatement>) -> Vec<Statement> {
    stmts.into_iter().map(Into::into).collect()
}

impl From<PavoPatterns> for Patterns {
    fn from(pats: PavoPatterns) -> Patterns {
        Patterns(pats.0, pats.1, pats.2.map(|guard| guard.into()))
    }
}
