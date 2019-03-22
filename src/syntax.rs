//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Id<'a>(pub Span<'a>);

impl<'a> Id<'a> {
    pub fn new(id: &'a str) -> Id<'a> {
        Id(Span::new(CompleteStr(id)))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<'a>(pub Span<'a>, pub _Expression<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression<'a> {
    Nil,
    Bool(bool),
    Id(Id<'a>),
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
    Let(BinderPattern<'a>, Expression<'a>),
    Assign(Id<'a>, Expression<'a>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinderPattern<'a>(pub Span<'a>, pub _BinderPattern<'a>);

#[derive(Debug, Clone, PartialEq)]
pub enum _BinderPattern<'a> {
    Blank,
    Id(Id<'a>, bool), // true iff mutable
}

// Used during parsing to generate default `nil`s for missing stuff
impl<'a> Expression<'a> {
    pub fn nil() -> Expression<'static> {
        Expression(
            LocatedSpan::new(CompleteStr("")),
            _Expression::Nil,
        )
    }
}
