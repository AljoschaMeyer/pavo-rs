//! Desugared pavo syntax.
//!
//! Regular syntax is translated into this directly after parsing. The remaining layers of the
//! program are only aware of this more manageable pavo subset.

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

use crate::syntax::{
    Id,
    Statement as PavoStatement,
    _Statement as _PavoStatement,
    Expression as PavoExpression,
    _Expression as _PavoExpression,
    BinderPattern,
    _BinderPattern,
};

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<'a>(pub Span<'a>, pub _Expression<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression<'a> {
    Nil,
    Bool(bool),
    Id(Id<'a>),
    If(Box<Expression<'a>>, Vec<Statement<'a>>, Vec<Statement<'a>>),
    While(Box<Expression<'a>>, Vec<Statement<'a>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<'a>(pub Span<'a>, pub _Statement<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement<'a> {
    Expression(Expression<'a>),
    Return(Expression<'a>),
    Break(Expression<'a>),
    Let {
        id: Id<'a>,
        mutable: bool,
        rhs: Expression<'a>,
    }
}

// Functions for generating ast nodes during desugaring. They have bogus source locations. The
// `&'a str` arguments are an easy way to handle the lifetime requirements, they can be empty.

impl<'a> Expression<'a> {
    pub fn nil() -> Expression<'static> {
        Expression(
            LocatedSpan::new(CompleteStr("")),
            _Expression::Nil,
        )
    }

    pub fn bool_(b: bool) -> Expression<'static> {
        Expression(
            LocatedSpan::new(CompleteStr("")),
            _Expression::Bool(b)
        )
    }

    pub fn if_(cond: Box<Expression<'a>>, then_block: Vec<Statement<'a>>, else_block: Vec<Statement<'a>>) -> Expression<'a> {
        Expression(
            LocatedSpan::new(CompleteStr("")),
            _Expression::If(cond, then_block, else_block)
        )
    }

    pub fn id(the_id: Id<'a>) -> Expression<'a> {
        Expression(
            LocatedSpan::new(CompleteStr("")),
            _Expression::Id(the_id)
        )
    }
}

impl<'a> Statement<'a> {
    pub fn exp(e: Expression<'a>) -> Statement<'a> {
        Statement(
            LocatedSpan::new(CompleteStr("")),
            _Statement::Expression(e)
        )
    }

    pub fn let_(id: Id<'a>, mutable: bool, rhs: Expression<'a>) -> Statement<'a> {
        Statement(
            LocatedSpan::new(CompleteStr("")),
            _Statement::Let { id, mutable, rhs }
        )
    }
}

impl<'a> From<PavoExpression<'a>> for Expression<'a> {
    fn from(exp: PavoExpression<'a>) -> Self {
        Expression(exp.0, match exp.1 {
            _PavoExpression::Nil => _Expression::Nil,
            _PavoExpression::Bool(b) => _Expression::Bool(b),
            _PavoExpression::Id(id) => _Expression::Id(id),
            _PavoExpression::If(cond, then_block, else_block) => _Expression::If(
                cond.into(),
                desugar_statements(then_block),
                desugar_statements(else_block),
            ),
            _PavoExpression::Land(lhs, rhs) => _Expression::If(
                lhs.into(),
                vec![Statement::exp(Expression::if_(
                    rhs.into(),
                    vec![Statement::exp(Expression::bool_(true))],
                    vec![Statement::exp(Expression::bool_(false))]
                ))],
                vec![Statement::exp(Expression::bool_(false))],
            ),
            _PavoExpression::Lor(lhs, rhs) => _Expression::If(
                lhs.into(),
                vec![Statement::exp(Expression::bool_(true))],
                vec![Statement::exp(Expression::if_(
                    rhs.into(),
                    vec![Statement::exp(Expression::bool_(true))],
                    vec![Statement::exp(Expression::bool_(false))]
                ))],
            ),
            _PavoExpression::While(cond, body) => _Expression::While(
                cond.into(),
                desugar_statements(body),
            ),
        })
    }
}

pub fn desugar_statements<'a>(stmts: Vec<PavoStatement<'a>>) -> Vec<Statement<'a>> {
    stmts.into_iter().flat_map(|stmt| desugar_statement(stmt).into_iter()).collect()
}

fn desugar_statement<'a>(stmt: PavoStatement<'a>) -> Vec<Statement<'a>> {
    match stmt.1 {
        _PavoStatement::Expression(exp) => vec![Statement(
            stmt.0, _Statement::Expression(exp.into())
        )],
        _PavoStatement::Return(exp) => vec![Statement(
            stmt.0, _Statement::Return(exp.into())
        )],
        _PavoStatement::Break(exp) => vec![Statement(
            stmt.0, _Statement::Break(exp.into())
        )],
        _PavoStatement::Let(pat, rhs) => {
            std::iter::once(Statement(
               stmt.0, _Statement::Let { id: Id::new(PAT), mutable: true, rhs: rhs.into() }
           )).chain(desugar_binder_pattern(pat).into_iter()).collect::<Vec<_>>()
        }
    }
}

// special str used as a prefix for the "identifiers" generated during pattern desugaring
const PAT: &str = "ß";

fn desugar_binder_pattern<'a>(pat: BinderPattern<'a>) -> Vec<Statement<'a>> {
    match pat.1 {
        _BinderPattern::Blank => vec![],
        _BinderPattern::Id(id, mutable) => {
            vec![Statement::let_(id, mutable, Expression::id(Id::new(PAT)))]
        }
    }
}

impl<'a> From<Box<PavoExpression<'a>>> for Box<Expression<'a>> {
    fn from(stmt: Box<PavoExpression<'a>>) -> Self {
        Box::new((*stmt).into())
    }
}
