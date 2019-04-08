//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

// use std::collections::BTreeSet;

use crate::util::SrcLocation;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub String, pub SrcLocation);

impl Id {
    pub fn new(id: &str, loc: SrcLocation) -> Id {
        Id(id.to_string(), loc)
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
    If(Box<Expression>, Vec<Statement>, Option<Vec<Statement>>),
    Land(Box<Expression>, Box<Expression>),
    Lor(Box<Expression>, Box<Expression>),
    While(Box<Expression>, Vec<Statement>),
    Try(Vec<Statement>, Patterns, Vec<Statement>, Option<Vec<Statement>>),
    QM(Box<Expression>),
    Invocation(Box<Expression>, Vec<Expression>),
    Method(Box<Expression>, Box<Expression>, Vec<Expression>), // The second expression is restricted to valid method_exps
    BinOp(Box<Expression>, BinOp, Box<Expression>),
    Array(Vec<Expression>),
    Fun(ArrayPattern, Vec<Statement>),
    Case(Box<Expression>, Vec<(Patterns, Vec<Statement>)>),
    Loop(Box<Expression>, Vec<(Patterns, Vec<Statement>)>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Eq, Subtract
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

impl Patterns {
    pub fn dummy(pats: Vec<Pattern>) -> Patterns {
        Patterns(
            SrcLocation::default(),
            pats,
            None
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pattern(pub SrcLocation, pub _Pattern);

#[derive(Debug, Clone, PartialEq)]
pub enum _Pattern {
    Blank,
    Id(Id, bool), // true iff mutable
    Nil,
    Bool(bool),
    Int(i64),
    Array(ArrayPattern),
}

impl Pattern {
    fn dummy(p: _Pattern) -> Pattern {
        Pattern(SrcLocation::default(), p)
    }

    pub fn blank() -> Pattern {
        Pattern::dummy(_Pattern::Blank)
    }

    pub fn nil() -> Pattern {
        Pattern::dummy(_Pattern::Nil)
    }

    pub fn bool_(b: bool) -> Pattern {
        Pattern::dummy(_Pattern::Bool(b))
    }

    pub fn arr(arr: ArrayPattern) -> Pattern {
        Pattern::dummy(_Pattern::Array(arr))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayPattern(pub Vec<Pattern>, pub ArrayPatternOptionals, pub Vec<Pattern>);

impl ArrayPattern {
    pub fn empty() -> ArrayPattern {
        ArrayPattern(vec![], ArrayPatternOptionals::empty(), vec![])
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ArrayPatternOptionals {
    Left(Vec<Pattern>, Option<Option<(Id, bool)>>),
    Right(Option<Option<(Id, bool)>>, Vec<Pattern>),
}

impl ArrayPatternOptionals {
    pub fn empty() -> ArrayPatternOptionals {
        ArrayPatternOptionals::Left(vec![], None)
    }
}

impl Expression {
    fn dummy(exp: _Expression) -> Expression {
        Expression(SrcLocation::default(), exp)
    }

    pub fn nil() -> Expression {
        Expression::dummy(_Expression::Nil)
    }

    pub fn bool_(b: bool) -> Expression {
        Expression::dummy(_Expression::Bool(b))
    }

    pub fn if_(
        cond: Box<Expression>,
        then_block: Vec<Statement>,
        else_block: Option<Vec<Statement>>,
    ) -> Expression {
        Expression::dummy(_Expression::If(cond, then_block, else_block))
    }

    pub fn try_(
        try_block: Vec<Statement>,
        pat: Patterns,
        catch_block: Vec<Statement>,
        finally_block: Option<Vec<Statement>>
    ) -> Expression {
        Expression::dummy(_Expression::Try(try_block, pat, catch_block, finally_block))
    }

    pub fn invocation(fun: Box<Expression>, args: Vec<Expression>) -> Expression {
        Expression::dummy(_Expression::Invocation(fun, args))
    }

    pub fn case(matcher: Box<Expression>, arms: Vec<(Patterns, Vec<Statement>)>) -> Expression {
        Expression::dummy(_Expression::Case(matcher, arms))
    }
}

impl Statement {
    fn dummy(stmt: _Statement) -> Statement {
        Statement(SrcLocation::default(), stmt)
    }

    pub fn exp(expr: Expression) -> Statement {
        Statement::dummy(_Statement::Expression(expr))
    }
}
