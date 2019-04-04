//! The syntax defines the (context-free) structure of valid pavo programs.
//!
//! Pavo uses C-like syntax, devided into expressions and statements. Statements can be chained
//! with semicolons.

use std::collections::BTreeSet;

use crate::util::SrcLocation;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub String, pub SrcLocation);

impl Id {
    pub fn new(id: &str, loc: SrcLocation) -> Id {
        Id(id.to_string(), loc)
    }

    pub fn dummy(id: &str) -> Id {
        Id::new(id, SrcLocation::default())
    }

    pub fn pat(level: usize) -> Id {
        Id::dummy(&format!("{}{}", "ß", level))
    }

    pub fn caught() -> Id {
        Id::dummy("ü")
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
    Land(Box<Expression>, Box<Expression>),
    Lor(Box<Expression>, Box<Expression>),
    While(Box<Expression>, Vec<Statement>),
    Try(Vec<Statement>, BinderPatterns, Vec<Statement>, Vec<Statement>),
    QM(Box<Expression>),
    Invocation(Box<Expression>, Vec<Expression>),
    Method(Box<Expression>, Box<Expression>, Vec<Expression>), // The second expression is restricted to valid method_exps
    BinOp(Box<Expression>, BinOp, Box<Expression>),
    Array(Vec<Expression>),
    Fun(OuterArrayPattern, Vec<Statement>),
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
    Let(BinderPatterns, Expression),
    Assign(Id, Expression),
    Rec(Vec<(Id, OuterArrayPattern, Vec<Statement>)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinderPatterns(pub SrcLocation, pub Vec<BinderPattern>, pub Option<Box<Expression>>);

impl BinderPatterns {
    pub fn blank() -> BinderPatterns {
        BinderPatterns(
            SrcLocation::default(),
            vec![BinderPattern::blank()],
            None
        )
    }
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

    pub fn arr_from_ids(ids: &BTreeSet<(String, bool)>) -> BinderPattern {
        BinderPattern(
            SrcLocation::default(),
            _BinderPattern::Array(OuterArrayPattern(
                SrcLocation::default(),
                _OuterArrayPattern::Closed(ids.iter().map(|(id, mutable)| ArrayPattern(
                    SrcLocation::default(),
                    _ArrayPattern::Regular(BinderPattern(
                        SrcLocation::default(),
                        _BinderPattern::Id(Id::dummy(id), *mutable)
                    ))
                )).collect())
            ))
        )
    }

    // Return all identifiers bound by this pattern, and whether the binding is mutable.
    // Returns `Err` if an identifier is bound multiple times.
    pub fn bindings(&self) -> Result<BTreeSet<(String, bool)>, Id> {
        let mut ret = BTreeSet::new();
        self.1.add_bindings(&mut ret)?;
        return Ok(ret);
    }
}

impl _BinderPattern {
    // Returns `Err` if an identifier is bound multiple times.
    fn add_bindings(&self, m: &mut BTreeSet<(String, bool)>) -> Result<(), Id> {
        match self {
            _BinderPattern::Blank => Ok(()),
            _BinderPattern::Id(id, mutable) => {
                if !m.insert((id.0.clone(), *mutable)) {
                    Err(id.clone())
                } else if m.contains(&(id.0.clone(), !*mutable)) {
                    return Err(id.clone())
                } else {
                    Ok(())
                }
            }
            _BinderPattern::Array(OuterArrayPattern(_, oap)) => oap.add_bindings(m)
        }
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

impl _OuterArrayPattern {
    // Returns `Err` if an identifier is bound multiple times.
    fn add_bindings(&self, m: &mut BTreeSet<(String, bool)>) -> Result<(), Id> {
        match self {
            _OuterArrayPattern::Closed(pats) | _OuterArrayPattern::Open(pats) => {
                for ArrayPattern(_, p) in pats {
                    p.add_bindings(m)?
                }
                Ok(())
            }
            _OuterArrayPattern::OpenNamed(pats, id, mutable) => {
                if !m.insert((id.0.clone(), *mutable)) {
                    Err(id.clone())
                } else if m.contains(&(id.0.clone(), !*mutable)) {
                    return Err(id.clone())
                } else {
                    for ArrayPattern(_, p) in pats {
                        p.add_bindings(m)?
                    }
                    Ok(())
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayPattern(pub SrcLocation, pub _ArrayPattern);

#[derive(Debug, Clone, PartialEq)]
pub enum _ArrayPattern {
    QM(Id, bool), // true iff mutable
    Regular(BinderPattern)
}

impl _ArrayPattern {
    // Returns `Err` if an identifier is bound multiple times.
    fn add_bindings(&self, m: &mut BTreeSet<(String, bool)>) -> Result<(), Id> {
        match self {
            _ArrayPattern::QM(id, mutable) => {
                if !m.insert((id.0.clone(), *mutable)) {
                    Err(id.clone())
                } else if m.contains(&(id.0.clone(), !*mutable)) {
                    return Err(id.clone())
                } else {
                    Ok(())
                }
            }
            _ArrayPattern::Regular(p) => p.1.add_bindings(m),
        }
    }
}

impl ArrayPattern {
    pub fn is_regular(&self) -> bool {
        match self.1 {
            _ArrayPattern::Regular(..) => true,
            _ => false,
        }
    }
}

// Used during parsing to generate default `nil`s for missing stuff
impl Expression {
    pub fn nil() -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Nil,
        )
    }

    pub fn id(id: &str) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Id(Id::dummy(id)),
        )
    }

    pub fn array(inners: Vec<Expression>) -> Expression {
        Expression(
            SrcLocation::default(),
            _Expression::Array(inners),
        )
    }

    pub fn try_(
        try_block: Vec<Statement>,
        pat: BinderPatterns,
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

    pub fn throw_nil() -> Statement {
        Statement(
            SrcLocation::default(),
            _Statement::Throw(Expression::nil()),
        )
    }
}
