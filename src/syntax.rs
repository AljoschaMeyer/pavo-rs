//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<'a>(pub Span<'a>, pub _Expression<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression<'a> {
    Nil,
    Bool(bool),
    If(Box<Expression<'a>>, Vec<Statement<'a>>, Vec<Statement<'a>>),
    Land(Box<Expression<'a>>, Box<Expression<'a>>),
    Lor(Box<Expression<'a>>, Box<Expression<'a>>),
    While(Box<Expression<'a>>, Vec<Statement<'a>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<'a>(pub Span<'a>, pub _Statement<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement<'a> {
    Expression(Expression<'a>),
    Return(Expression<'a>),
    Break(Expression<'a>),
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
}

impl<'a> Statement<'a> {
    pub fn exp(e: Expression<'a>) -> Statement<'a> {
        Statement(
            LocatedSpan::new(CompleteStr("str_for_the_lifetime")),
            _Statement::Expression(e)
        )
    }
}
