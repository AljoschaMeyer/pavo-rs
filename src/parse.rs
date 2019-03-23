// Convert well-formed pavo source code into a syntax tree.
//
// The parsers consume all trailing whitespace, but do not skip over leading whitespace.

use failure_derive::Fail;
use nom::{
    {line_ending, not_line_ending, multispace1, eof},
    {value, tag, take_while1, one_of},
    {do_parse, alt, many0, many1, opt, fold_many0, many_m_n},
    {delimited, separated_list},
    {named, not, map, try_parse},
    types::CompleteStr, IResult, Err, Context, ErrorKind,
};
use nom_locate::{LocatedSpan, position};

use crate::syntax::{
    Id,
    Expression, _Expression,
    Statement, _Statement,
    BinderPattern, _BinderPattern,
};
use crate::util::SrcLocation;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

named!(linecomment(Span) -> (), do_parse!(
    tag!("#") >>
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

macro_rules! kw(
    ($i:expr, $kw:expr) => ({
        do_parse!(
            $i,
            tag!($kw) >>
            not!(take_while1!(is_id_char)) /* ensure this is not a prefix of an identifier*/ >>
            ws0 >>
            (())
        )
    });
    ($i:expr, $f:expr) => (
        opt!($i, call!($f));
    );
);

named!(semi(Span) -> (), do_parse!(tag!(";") >> ws0 >> (())));
named!(lbrace(Span) -> (), do_parse!(tag!("{") >> ws0 >> (())));
named!(rbrace(Span) -> (), do_parse!(tag!("}") >> ws0 >> (())));
named!(lparen(Span) -> (), do_parse!(tag!("(") >> ws0 >> (())));
named!(rparen(Span) -> (), do_parse!(tag!(")") >> ws0 >> (())));
named!(land(Span) -> (), do_parse!(tag!("&&") >> ws0 >> (())));
named!(lor(Span) -> (), do_parse!(tag!("||") >> ws0 >> (())));
named!(blank(Span) -> (), do_parse!(tag!("_") >> ws0 >> (())));
named!(assign(Span) -> (), do_parse!(tag!("=") >> ws0 >> (())));
named!(qm(Span) -> (), do_parse!(tag!("?") >> ws0 >> (())));

fn is_id_char(c: char) -> bool {
    return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c == '_');
}

fn id<'a>(i: Span<'a>) -> IResult<Span<'a>, Id> {
    let (i1, maybe_underscore) = try_parse!(i, opt!(tag!("_")));
    let (remaining, len) = if maybe_underscore.is_some() {
        try_parse!(i1, do_parse!(
            len: map!(
                many_m_n!(1, 254, one_of!("0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")),
                |tail| 1 + tail.len()
            ) >>
            not!(take_while1!(is_id_char)) /* ensure the id isn't even longer */ >>
            ws0 >>
            (len)
        ))
    } else {
        try_parse!(i1, do_parse!(
            one_of!("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") >>
            len: map!(
                many_m_n!(0, 254, one_of!("0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")),
                |tail| 1 + tail.len()
            ) >>
            not!(take_while1!(is_id_char)) /* ensure the id isn't even longer */ >>
            ws0 >>
            (len)
        ))
    };

    let the_id_str = &i.fragment[..len];
    let mut the_id = i.clone();
    the_id.fragment = CompleteStr(the_id_str);

    if is_kw(the_id_str) {
        Err(Err::Error(Context::Code(remaining, ErrorKind::Custom(0))))
    } else {
        Ok((remaining, Id(the_id)))
    }
}

fn is_kw(id: &str) -> bool {
    id == "nil" || id == "true" || id == "false" || id == "if" || id == "else" ||
    id == "return" || id == "break" || id == "while" || id == "mut" || id == "loop" ||
    id == "case" || id == "throw" || id == "try" || id == "catch" || id == "finally" ||
    id == "async" || id == "await" || id == "for" || id == "nan" || id == "inf" ||
    id == "let"
}

named!(exp_id(Span) -> Expression, do_parse!(
    pos: position!() >>
    the_id: id >>
    (Expression(pos, _Expression::Id(the_id)))
));

named!(exp_nil(Span) -> Expression, do_parse!(
    pos: position!() >>
    kw!("nil") >>
    (Expression(pos, _Expression::Nil))
));

named!(exp_bool(Span) -> Expression, do_parse!(
    pos: position!() >>
    b: alt!(value!(true, kw!("true")) | value!(false, kw!("false"))) >>
    (Expression(pos, _Expression::Bool(b)))
));

// Expressions that do not contain other expressions.
named!(exp_atomic(Span) -> Expression, alt!(
    exp_nil | exp_bool | exp_id
));

named!(exp_if(Span) -> Expression, do_parse!(
    pos: position!() >>
    kw!("if") >>
    cond: map!(exp, Box::new) >>
    if_block: block >>
    else_block: map!(
        opt!(do_parse!(
            kw!("else") >>
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
    kw!("while") >>
    cond: map!(exp, Box::new) >>
    loop_block: block >>
    (Expression(pos, _Expression::While(cond, loop_block)))
));

named!(exp_try(Span) -> Expression, do_parse!(
    pos: position!() >>
    kw!("try") >>
    try_block: block >>
    kw!("catch") >>
    pat: binder_pat >>
    catch_block: block >>
    finally_block: map!(
        opt!(do_parse!(
            kw!("finally") >>
            finally_block: block >>
            (finally_block)
        )),
        |blck| blck.unwrap_or(vec![])
    ) >>
    (Expression(pos, _Expression::Try(try_block, pat, catch_block, finally_block)))
));

// Expressions that can follow an `else` keyword without being enclosed in braces.
named!(exp_blocky(Span) -> Expression, alt!(
    exp_if | exp_while | exp_try
));

// 1300 is the precedence level
// `::`
// named!(exp_binop_1300(Span) -> Expression, non_leftrecursive_exp);
named!(exp_binop_1300(Span) -> Expression, do_parse!(expr: non_leftrecursive_exp >> (expr)));

// 1200 is the precedence level
// `field access`
named!(exp_binop_1200(Span) -> Expression, do_parse!(expr: exp_binop_1300 >> (expr)));

// 1100 is the precedence level
// `call, index`
named!(exp_binop_1100(Span) -> Expression, do_parse!(expr: exp_binop_1200 >> (expr)));

// 1000 is the precedence level
// `-, !` (unary)
named!(exp_binop_1000(Span) -> Expression, do_parse!(expr: exp_binop_1100 >> (expr)));

// 900 is the precedence level
// `?`
named!(exp_binop_900(Span) -> Expression, do_parse!(
    pos: position!() >>
    first: exp_binop_1000 >>
    fold: fold_many0!(
        do_parse!(
            qm >>
            (Expression::nil())
        ),
        first,
        |acc, _| Expression(pos, _Expression::QM(Box::new(acc)))
    ) >>
    (fold)
));

// 800 is the precedence level
// `*, /, %`
named!(exp_binop_800(Span) -> Expression, do_parse!(expr: exp_binop_900 >> (expr)));

// 700 is the precedence level
// `+, -` (binary operators)
named!(exp_binop_700(Span) -> Expression, do_parse!(expr: exp_binop_800 >> (expr)));

// 600 is the precedence level
// `<<, >>`
named!(exp_binop_600(Span) -> Expression, do_parse!(expr: exp_binop_700 >> (expr)));

// 500 is the precedence level
// `&`
named!(exp_binop_500(Span) -> Expression, do_parse!(expr: exp_binop_600 >> (expr)));

// 400 is the precedence level
// `^`
named!(exp_binop_400(Span) -> Expression, do_parse!(expr: exp_binop_500 >> (expr)));

// 300 is the precedence level
// `|`
named!(exp_binop_300(Span) -> Expression, do_parse!(expr: exp_binop_400 >> (expr)));

// 200 is the precedence level
// `==, !=, <, <=, >, >=`
named!(exp_binop_200(Span) -> Expression, do_parse!(expr: exp_binop_300 >> (expr)));

// 100 is the precedence level
// `&&`
named!(exp_binop_100(Span) -> Expression, do_parse!(
    pos: position!() >>
    first: exp_binop_200 >>
    fold: fold_many0!(
        do_parse!(
            land >>
            expr: exp_binop_200 >>
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
// `||`
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
    kw!("return") >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Return(expr)))
));

named!(stmt_break(Span) -> Statement, do_parse!(
    pos: position!() >>
    kw!("break") >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Break(expr)))
));

named!(stmt_throw(Span) -> Statement, do_parse!(
    pos: position!() >>
    kw!("throw") >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Throw(expr)))
));

named!(stmt_let(Span) -> Statement, do_parse!(
    pos: position!() >>
    kw!("let") >>
    pat: binder_pat >>
    assign >>
    expr: exp >>
    (Statement(pos, _Statement::Let(pat, expr)))
));

named!(stmt_assign(Span) -> Statement, do_parse!(
    pos: position!() >>
    the_id: id >>
    assign >>
    expr: exp >>
    ws0 >>
    (Statement(pos, _Statement::Assign(the_id, expr)))
));

named!(stmt(Span) -> Statement, alt!(
    stmt_assign |
    stmt_exp |
    stmt_return |
    stmt_break |
    stmt_throw |
    stmt_let
));

named!(stmts0(Span) -> Vec<Statement>, separated_list!(semi, stmt));

named!(block(Span) -> Vec<Statement>, delimited!(lbrace, stmts0, rbrace));

named!(pattern_id(Span) -> (Id, bool), do_parse!(
    mutable: map!(opt!(kw!("mut")), |maybe| maybe.is_some()) >>
    binder: id >>
    ((binder, mutable))
));

named!(binder_id(Span) -> BinderPattern, do_parse!(
    pos: position!() >>
    pat: map!(pattern_id, |(binder, mutable)| _BinderPattern::Id(binder, mutable)) >>
    (BinderPattern(pos, pat))
));

named!(binder_blank(Span) -> BinderPattern, do_parse!(
    pos: position!() >>
    pat: value!(_BinderPattern::Blank, blank) >>
    (BinderPattern(pos, pat))
));

named!(binder_pat(Span) -> BinderPattern, alt!(
    binder_id |
    binder_blank
));

named!(p_script(Span) -> Vec<Statement>, do_parse!(
    ws0 >>
    sts: stmts0 >>
    eof!() >>
    (sts)
));

pub fn script<'a>(i: Span<'a>) -> Result<Vec<Statement>, ParseError> {
    match p_script(i) {
        Ok((_, stmts)) => return Ok(stmts),
        Err(Err::Incomplete(_)) => unreachable!(),
        Err(Err::Error(cx)) | Err(Err::Failure(cx)) => {
            let location = match cx {
                Context::Code(i, _) => SrcLocation::from_span(&i),
                // Context::List(cxs) => SrcLocation::from_span(cxs[0].0),
            };

            return Err(ParseError {
                location,
                kind: cx.into_error_kind(),
            });
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Hash, Fail)]
#[fail(display = "Parse error at {:?}: {:?}", location, kind)]
pub struct ParseError {
    location: SrcLocation,
    kind: ErrorKind,
}
