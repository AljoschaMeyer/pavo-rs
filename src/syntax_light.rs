//! Desugared pavo syntax.
//!
//! Regular syntax is translated into this directly after parsing. The remaining layers of the
//! program are only aware of this more manageable pavo subset.

use crate::syntax::{
    Id,
    Statement as PavoStatement,
    _Statement as _PavoStatement,
    Expression as PavoExpression,
    _Expression as _PavoExpression,
    BinOp,
    BinderPattern,
    _BinderPattern,
    OuterArrayPattern, _OuterArrayPattern,
    ArrayPattern, _ArrayPattern,
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
}

// Functions for generating ast nodes during desugaring. They have bogus source locations. The
// `&'a str` arguments are an easy way to handle the lifetime requirements, they can be empty.

impl Expression {
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
}

impl From<PavoExpression> for Expression {
    fn from(exp: PavoExpression) -> Expression {
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
            _PavoExpression::Try(try_block, binder, caught_block, finally_block) => {
                let mut caught_buf = vec![Statement::let_(Id::pat(0), false, Expression::thrown())];
                desugar_binder_pattern(binder, &mut caught_buf);
                do_desugar_statements(caught_block, &mut caught_buf);
                _Expression::Try(
                    desugar_statements(try_block),
                    caught_buf,
                    desugar_statements(finally_block)
                )
            },
            _PavoExpression::QM(inner) => Self::from(PavoExpression::try_(
                vec![PavoStatement::exp((*inner).into())],
                BinderPattern::blank(),
                vec![PavoStatement::exp(PavoExpression::nil())],
                vec![]
            )).1,
            _PavoExpression::Invocation(fun, args) => _Expression::Invocation(
                fun.into(),
                args.into_iter().map(Into::into).collect()
            ),
            _PavoExpression::Method(first_arg, fun_id, remaining_args) => _Expression::Invocation(
                Box::new(Expression::id(fun_id)),
                std::iter::once((*first_arg).into())
                    .chain(remaining_args.into_iter().map(Into::into))
                    .collect()
            ),
            _PavoExpression::BinOp(lhs, op, rhs) => match op {
                BinOp::Eq => _Expression::Builtin2(
                    W(builtins::eq),
                    lhs.into(),
                    rhs.into()
                ),
            }
            _PavoExpression::Array(inners) => _Expression::BuiltinMany(
                W(builtins::arr_new),
                inners.into_iter().map(Into::into).collect()
            ),
            _PavoExpression::Fun(args, body) => {
                let mut stmts = vec![Statement::let_(Id::pat(0), false, Expression::args())];

                do_desugar_binder_outer_array_pattern(args, &mut stmts, 0);
                do_desugar_statements(body, &mut stmts);

                _Expression::Fun(stmts)
            }
        })
    }
}

impl From<Box<PavoExpression>> for Box<Expression> {
    fn from(stmt: Box<PavoExpression>) -> Self {
        Box::new((*stmt).into())
    }
}

pub fn desugar_statements(stmts: Vec<PavoStatement>) -> Vec<Statement> {
    let mut buf = vec![];
    do_desugar_statements(stmts, &mut buf);
    buf
}

fn do_desugar_statements(stmts: Vec<PavoStatement>, buf: &mut Vec<Statement>) {
    for stmt in stmts.into_iter() {
        desugar_statement(stmt, buf);
    }
}

fn desugar_statement(stmt: PavoStatement, buf: &mut Vec<Statement>) {
    match stmt.1 {
        _PavoStatement::Expression(exp) => buf.push(Statement(
            stmt.0, _Statement::Expression(exp.into())
        )),
        _PavoStatement::Return(exp) => buf.push(Statement(
            stmt.0, _Statement::Return(exp.into())
        )),
        _PavoStatement::Break(exp) => buf.push(Statement(
            stmt.0, _Statement::Break(exp.into())
        )),
        _PavoStatement::Throw(exp) => buf.push(Statement(
            stmt.0, _Statement::Throw(exp.into())
        )),
        _PavoStatement::Let(pat, rhs) => {
            buf.push(Statement(
                stmt.0,
                _Statement::Let { id: Id::pat(0), mutable: false, rhs: rhs.into() }
            ));
            desugar_binder_pattern(pat, buf);
        }
        _PavoStatement::Assign(id, exp) => buf.push(Statement(
            stmt.0, _Statement::Assign(id, exp.into())
        )),
    }
}

fn desugar_binder_pattern(pat: BinderPattern, buf: &mut Vec<Statement>) {
    do_desugar_binder_pattern(pat, buf, 0)
}

fn do_desugar_binder_pattern(pat: BinderPattern, buf: &mut Vec<Statement>, level: usize) {
    match pat.1 {
        _BinderPattern::Blank => { /* no-op */ },
        _BinderPattern::Id(id, mutable) => {
            buf.push(Statement::let_(id, mutable, Expression::id(Id::pat(level))));
        }
        _BinderPattern::Array(p @ OuterArrayPattern(..)) => do_desugar_binder_outer_array_pattern(p, buf, level),
    }
}

fn do_desugar_binder_array_pattern(pat: ArrayPattern, buf: &mut Vec<Statement>, level: usize) {
    match pat.1 {
        _ArrayPattern::Regular(inner) => do_desugar_binder_pattern(inner, buf, level),
        _ArrayPattern::QM(id, mutable) => {
            buf.push(Statement::let_(id, mutable, Expression::id(Id::pat(level))));
        }
    }
}

fn do_desugar_binder_outer_array_pattern(OuterArrayPattern(src, p): OuterArrayPattern, buf: &mut Vec<Statement>, level: usize) {
    buf.push(Statement::exp(Expression(src, _Expression::Builtin1(
        W(builtins::assert_arr),
        Box::new(Expression::id(Id::pat(level)))
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
                        id: Id::pat(level + 1),
                        mutable: false,
                        rhs: Expression(src, _Expression::Builtin2(
                            if inner.is_regular() {
                                W(builtins::arr_get)
                            } else {
                                W(builtins::arr_get_or_nil)
                            },
                            Box::new(Expression::id(Id::pat(level))),
                            Box::new(Expression::int_usize(i))
                        ))
                    }
                ));
                do_desugar_binder_array_pattern(inner, buf, level + 1);
            }

            if !open {
                buf.push(Statement::exp(Expression(src, _Expression::Builtin2(
                    W(builtins::assert_arr_len_at_most),
                    Box::new(Expression::id(Id::pat(level))),
                    Box::new(Expression::int_usize(num_inners))
                ))));
            }

            if let Some((id, mutable)) = named_remaining {
                buf.push(Statement::let_(id.clone(), mutable, Expression(src, _Expression::Builtin2(
                    W(builtins::arr_splice_suffix_helpful),
                    Box::new(Expression::id(Id::pat(level))),
                    Box::new(Expression::int_usize(num_inners))
                ))));
            }
        }
    }
}
