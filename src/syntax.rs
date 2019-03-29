//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

use crate::util::SrcLocation;

#[derive(Debug, Clone, PartialEq)]
pub struct Id(pub String, pub SrcLocation);

impl Id {
    pub fn new(id: &str, loc: SrcLocation) -> Id {
        Id(id.to_string(), loc)
    }

    pub fn dummy(id: &str) -> Id {
        Id::new(id, SrcLocation::default())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression(pub SrcLocation, pub _Expression);

#[derive(Debug, Clone, PartialEq)]
pub enum _Expression {
    Nil,
    Bool(bool),
    Id(Id),
    If(Box<Expression>, Vec<Statement>, Vec<Statement>),
    Land(Box<Expression>, Box<Expression>),
    Lor(Box<Expression>, Box<Expression>),
    While(Box<Expression>, Vec<Statement>),
    Try(Vec<Statement>, BinderPattern, Vec<Statement>, Vec<Statement>),
    QM(Box<Expression>),
    Invocation(Box<Expression>, Vec<Expression>),
    Method(Box<Expression>, Id, Vec<Expression>),
    BinOp(Box<Expression>, BinOp, Box<Expression>),
    Array(Vec<Expression>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Eq
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement(pub SrcLocation, pub _Statement);

#[derive(Debug, Clone, PartialEq)]
pub enum _Statement {
    Expression(Expression),
    Return(Expression),
    Break(Expression),
    Throw(Expression),
    Let(BinderPattern, Expression),
    Assign(Id, Expression),
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinderPattern(pub SrcLocation, pub _BinderPattern);

#[derive(Debug, Clone, PartialEq)]
pub enum _BinderPattern {
    Blank,
    Id(Id, bool), // true iff mutable
    Array(OuterArrayPattern)
}

impl BinderPattern {
    pub fn blank() -> BinderPattern {
        BinderPattern(
            SrcLocation::default(),
            _BinderPattern::Blank
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct OuterArrayPattern(pub SrcLocation, pub _OuterArrayPattern);

#[derive(Debug, Clone, PartialEq)]
pub enum _OuterArrayPattern {
    Closed(Vec<ArrayPattern>),
    Open(Vec<ArrayPattern>),
    OpenNamed(Vec<ArrayPattern>, Id, bool), // true iff mutable
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayPattern(pub SrcLocation, pub _ArrayPattern);

#[derive(Debug, Clone, PartialEq)]
pub enum _ArrayPattern {
    QM(Id, bool), // true iff mutable
    Regular(BinderPattern)
}

// Used during parsing to generate default `nil`s for missing stuff
impl Expression {
    pub fn nil() -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Nil,
        )
    }

    pub fn try_(
        try_block: Vec<Statement>,
        pat: BinderPattern,
        catch_block: Vec<Statement>,
        finally_block: Vec<Statement>
    ) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Try(try_block, pat, catch_block, finally_block),
        )
    }
}

impl Statement {
    pub fn exp(expr: Expression) -> Statement {
        Statement(
            SrcLocation::default(),
            _Statement::Expression(expr)
        )
    }
}
