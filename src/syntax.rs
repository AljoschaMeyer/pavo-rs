//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

pub struct Expression<'a>(pub Span<'a>, pub _Expression<'a>);

pub enum _Expression<'a> {
    Nil,
    Bool(bool),
    If(Box<Expression<'a>>, Box<[Statement<'a>]>, Box<[Statement<'a>]>),
}

pub struct Statement<'a>(pub Span<'a>, pub _Statement<'a>);

pub enum _Statement<'a> {
    Expression(Expression<'a>),
}
