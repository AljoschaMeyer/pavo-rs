// Convert well-formed pavo source code into a syntax tree.
//
// The parsers consume all trailing whitespace, but do not skip over leading whitespace.

use nom::{
    {line_ending, not_line_ending, multispace1, eof},
    {value, tag, take_while1},
    {do_parse, alt, many0, many1, opt, fold_many0},
    {delimited, separated_list_complete},
    {named, not, map},
    types::CompleteStr
};
use nom_locate::{LocatedSpan, position};

use crate::syntax::{
    Expression, _Expression,
    Statement, _Statement,
};

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

named!(linecomment(Span) -> (), do_parse!(
    tag!("//") >>
    many0!(not_line_ending) >>
    opt!(line_ending) >>
    (())
));

named!(ws(Span) -> (), alt!(
    value!((), linecomment) |
    value!((), multispace1)
));

named!(ws0(Span) -> (), do_parse!(
    many0!(ws) >>
    (())
));

named!(ws1(Span) -> (), do_parse!(
    many1!(ws) >>
    (())
));

named!(semi(Span) -> (), do_parse!(tag!(";") >> ws0 >> (())));
named!(lbrace(Span) -> (), do_parse!(tag!("{") >> ws0 >> (())));
named!(rbrace(Span) -> (), do_parse!(tag!("}") >> ws0 >> (())));
named!(lparen(Span) -> (), do_parse!(tag!("(") >> ws0 >> (())));
named!(rparen(Span) -> (), do_parse!(tag!(")") >> ws0 >> (())));
named!(land(Span) -> (), do_parse!(tag!("&&") >> ws0 >> (())));
named!(lor(Span) -> (), do_parse!(tag!("||") >> ws0 >> (())));

fn is_id_char(c: char) -> bool {
    return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c == '_');
}

named!(kw_nil(Span) -> (), do_parse!(
    tag!("nil") >>
    not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
    ws0 >>
    (())
));

named!(kw_true(Span) -> (), do_parse!(
    tag!("true") >>
    not!(take_while1!(is_id_char)) >>
    ws0 >>
    (())
));

named!(kw_false(Span) -> (), do_parse!(
    tag!("false") >>
    not!(take_while1!(is_id_char)) >>
    ws0 >>
    (())
));

named!(kw_if(Span) -> (), do_parse!(
    tag!("if") >>
    not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
    ws0 >>
    (())
));

named!(kw_else(Span) -> (), do_parse!(
    tag!("else") >>
    not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
    ws0 >>
    (())
));

named!(kw_return(Span) -> (), do_parse!(
    tag!("return") >>
    not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
    ws0 >>
    (())
));

named!(kw_break(Span) -> (), do_parse!(
    tag!("break") >>
    not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
    ws0 >>
    (())
));

named!(kw_while(Span) -> (), do_parse!(
    tag!("while") >>
    not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
    ws0 >>
    (())
));

named!(exp_nil(Span) -> Expression, do_parse!(
    pos: position!() >>
    kw_nil >>
    (Expression(pos, _Expression::Nil))
));

named!(exp_bool(Span) -> Expression, do_parse!(
    pos: position!() >>
    b: alt!(value!(true, kw_true) | value!(false, kw_false)) >>
    (Expression(pos, _Expression::Bool(b)))
));

// Expressions that do not contain other expressions.
named!(exp_atomic(Span) -> Expression, alt!(
    exp_nil | exp_bool
));

named!(exp_if(Span) -> Expression, do_parse!(
    pos: position!() >>
    kw_if >>
    cond: map!(exp, Box::new) >>
    if_block: block >>
    else_block: map!(
        opt!(do_parse!(
            kw_else >>
            else_block: alt!(
                block |
                map!(exp_blocky, |e| {
                    vec![Statement(e.0, _Statement::Expression(e))]
                })
            ) >>
            (else_block)
        )),
        |blck| blck.unwrap_or(vec![])
    ) >>
    (Expression(pos, _Expression::If(cond, if_block, else_block)))
));

named!(exp_while(Span) -> Expression, do_parse!(
    pos: position!() >>
    kw_while >>
    cond: map!(exp, Box::new) >>
    loop_block: block >>
    (Expression(pos, _Expression::While(cond, loop_block)))
));

// Expressions that can follow an `else` keyword without being enclosed in braces.
named!(exp_blocky(Span) -> Expression, alt!(
    exp_if | exp_while
));

// 100 is the precedence level
// `&&`
named!(exp_binop_100(Span) -> Expression, do_parse!(
    pos: position!() >>
    first: non_leftrecursive_exp >>
    fold: fold_many0!(
        do_parse!(
            land >>
            expr: non_leftrecursive_exp >>
            (expr)
        ),
        first,
        |acc, item| Expression(pos, _Expression::Land(Box::new(acc), Box::new(item)))
    ) >>
    (fold)
));

named!(non_leftrecursive_exp(Span) -> Expression, alt!(
    // expression wrapped in parens
    do_parse!(
        ex: delimited!(
            lparen,
            exp,
            rparen
        ) >>
        ws0 >>
        (ex)
    ) |
    exp_atomic |
    exp_blocky
));

// This is the left-recursive expression of the lowest precedence level
named!(exp(Span) -> Expression, do_parse!(
    pos: position!() >>
    first: exp_binop_100 >>
    fold: fold_many0!(
        do_parse!(
            lor >>
            expr: exp_binop_100 >>
            (expr)
        ),
        first,
        |acc, item| Expression(pos, _Expression::Lor(Box::new(acc), Box::new(item)))
    ) >>
    (fold)
));

named!(stmt_exp(Span) -> Statement, do_parse!(
    expr: exp >>
    (Statement(expr.0.clone(), _Statement::Expression(expr)))
));

named!(stmt_return(Span) -> Statement, do_parse!(
    pos: position!() >>
    kw_return >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Return(expr)))
));

named!(stmt_break(Span) -> Statement, do_parse!(
    pos: position!() >>
    kw_break >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Break(expr)))
));

named!(stmt(Span) -> Statement, alt!(
    stmt_exp |
    stmt_return |
    stmt_break
));

named!(stmts0(Span) -> Vec<Statement>, separated_list_complete!(semi, stmt));

named!(block(Span) -> Vec<Statement>, delimited!(lbrace, stmts0, rbrace));

named!(pub script(Span) -> Vec<Statement>, do_parse!(
    ws0 >>
    sts: stmts0 >>
    eof!() >>
    (sts)
));
