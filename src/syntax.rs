//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

pub struct Expression<'a>(pub Span<'a>, pub _Expression);

pub enum _Expression {
    Nil,
    Bool(bool),
}

pub struct Statement<'a>(pub Span<'a>, pub _Statement<'a>);

pub enum _Statement<'a> {
    Expression(Expression<'a>),
}
