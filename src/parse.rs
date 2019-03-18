// Convert well-formed pavo source code into a syntax tree.
//
// The parsers consume all trailing whitespace, but do not skip over leading whitespace.

use nom::{
    {line_ending, not_line_ending, multispace1, eof},
    {value, tag, take_while1},
    {do_parse, alt, many0, many1, opt},
    {delimited, separated_list_complete},
    {named, not},
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

named!(exp(Span) -> Expression, alt!(
    // expression wrapped in parens
    do_parse!(
        ex: delimited!(
            do_parse!(tag!("(") >> ws0 >> (())),
            exp,
            tag!(")")
        ) >>
        ws0 >>
        (ex)
    ) |
    exp_atomic
));

named!(stmt_exp(Span) -> Statement, do_parse!(
    ex: exp >>
    (Statement(ex.0.clone(), _Statement::Expression(ex)))
));

named!(stmt(Span) -> Statement, alt!(
    stmt_exp
));

named!(stmts0(Span) -> Vec<Statement>, separated_list_complete!(
    do_parse!(tag!(";") >> ws0 >> (())),
    stmt
));

named!(pub script(Span) -> Vec<Statement>, do_parse!(
    ws0 >>
    sts: stmts0 >>
    eof!() >>
    (sts)
));
