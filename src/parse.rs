// Convert well-formed pavo source code into a syntax tree.
//
// The parsers consume all trailing whitespace, but do not skip over leading whitespace.

use failure_derive::Fail;
use nom::{
    {line_ending, not_line_ending, multispace1, eof},
    {value, tag, take_while1, one_of, is_a},
    {do_parse, alt, many0, many1, opt, fold_many0, many_m_n},
    {delimited, separated_list, separated_nonempty_list},
    {named, not, map, try_parse},
    types::CompleteStr, IResult, Err, Context, ErrorKind,
};
use nom_locate::{LocatedSpan, position};

use crate::syntax::{
    Id,
    Expression, _Expression, BinOp,
    Statement, _Statement,
    BinderPattern, _BinderPattern,
    OuterArrayPattern, _OuterArrayPattern,
    ArrayPattern, _ArrayPattern,
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
named!(lbracket(Span) -> (), do_parse!(tag!("[") >> ws0 >> (())));
named!(rbracket(Span) -> (), do_parse!(tag!("]") >> ws0 >> (())));
named!(lparen(Span) -> (), do_parse!(tag!("(") >> ws0 >> (())));
named!(rparen(Span) -> (), do_parse!(tag!(")") >> ws0 >> (())));
named!(land(Span) -> (), do_parse!(tag!("&&") >> ws0 >> (())));
named!(lor(Span) -> (), do_parse!(tag!("||") >> ws0 >> (())));
named!(blank(Span) -> (), do_parse!(tag!("_") >> ws0 >> (())));
named!(assign(Span) -> (), do_parse!(tag!("=") >> ws0 >> (())));
named!(qm(Span) -> (), do_parse!(tag!("?") >> ws0 >> (())));
named!(comma(Span) -> (), do_parse!(tag!(",") >> ws0 >> (())));
named!(coloncolon(Span) -> (), do_parse!(tag!("::") >> ws0 >> (())));
named!(eq(Span) -> (), do_parse!(tag!("==") >> ws0 >> (())));
named!(dots(Span) -> (), do_parse!(tag!("...") >> ws0 >> (())));
named!(arrow(Span) -> (), do_parse!(tag!("->") >> ws0 >> (())));
named!(minus(Span) -> (), do_parse!(tag!("-") >> not!(tag!(">")) >> ws0 >> (())));

fn is_id_char(c: char) -> bool {
    return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c == '_');
}

fn id<'a>(i: Span<'a>) -> IResult<Span<'a>, Id> {
    let (i1, maybe_underscore) = try_parse!(i, opt!(tag!("_")));
    let (remaining, len) = if maybe_underscore.is_some() {
        try_parse!(i1, do_parse!(
            len: map!(
                many_m_n!(1, 254, one_of!("0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_")),
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
                many_m_n!(0, 254, one_of!("0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_")),
                |tail| 1 + tail.len()
            ) >>
            not!(take_while1!(is_id_char)) /* ensure the id isn't even longer */ >>
            ws0 >>
            (len)
        ))
    };

    let the_id_str = &i.fragment[..len];

    if is_kw(the_id_str) {
        Err(Err::Error(Context::Code(remaining, ErrorKind::Custom(0))))
    } else {
        Ok((remaining, Id::new(the_id_str, SrcLocation::from_span(&i))))
    }
}

fn is_kw(id: &str) -> bool {
    id == "nil" || id == "true" || id == "false" || id == "if" || id == "else" ||
    id == "return" || id == "break" || id == "while" || id == "mut" || id == "loop" ||
    id == "case" || id == "throw" || id == "try" || id == "catch" || id == "finally" ||
    id == "async" || id == "await" || id == "for" || id == "let" || id == "rec"
}

named!(exp_id(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    the_id: id >>
    (Expression(pos, _Expression::Id(the_id)))
));

named!(exp_nil(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("nil") >>
    (Expression(pos, _Expression::Nil))
));

named!(exp_bool(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    b: alt!(value!(true, kw!("true")) | value!(false, kw!("false"))) >>
    (Expression(pos, _Expression::Bool(b)))
));

fn hex_int<'a>(i: Span<'a>) -> IResult<Span<'a>, (SrcLocation, i64)> {
    let (i, (pos, digits)) = try_parse!(i, do_parse!(
        pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
        tag!("0x") >>
        digits: is_a!("0123456789abcdefABCDEF") >>
        ws0 >>
        ((pos, digits))
    ));

    match i64::from_str_radix(&digits.fragment.0, 16) {
        Ok(n) => Ok((i, (pos, n))),
        Err(_) => Err(Err::Error(Context::Code(i, ErrorKind::Custom(1))))
    }
}

fn dec_int<'a>(i: Span<'a>) -> IResult<Span<'a>, (SrcLocation, i64)> {
    let (i, (pos, digits)) = try_parse!(i, do_parse!(
        pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
        digits: is_a!("0123456789") >>
        ws0 >>
        ((pos, digits))
    ));

    match i64::from_str_radix(&digits.fragment.0, 10) {
        Ok(n) => Ok((i, (pos, n))),
        Err(_) => Err(Err::Error(Context::Code(i, ErrorKind::Custom(2))))
    }
}

named!(exp_hex_int(Span) -> Expression, map!(hex_int, |(pos, n)| Expression(pos, _Expression::Int(n))));
named!(exp_dec_int(Span) -> Expression, map!(dec_int, |(pos, n)| Expression(pos, _Expression::Int(n))));

named!(exp_num(Span) -> Expression, alt!(
    exp_hex_int | exp_dec_int
));

// Expressions that do not contain other expressions.
named!(exp_atomic(Span) -> Expression, alt!(
    exp_nil | exp_bool | exp_id | exp_num
));

named!(exp_if(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
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
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("while") >>
    cond: map!(exp, Box::new) >>
    loop_block: block >>
    (Expression(pos, _Expression::While(cond, loop_block)))
));

named!(exp_try(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
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

named!(fun(Span) -> (OuterArrayPattern, Vec<Statement>), do_parse!(
    args: alt!(
        do_parse!(
            pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
            lparen >>
            rparen >>
            (OuterArrayPattern(pos, _OuterArrayPattern::Closed(vec![])))
        ) |
        delimited!(
            lparen,
            outer_array_inners,
            rparen
        )
    ) >>
    arrow >>
    body: block >>
    ((args, body))
));

named!(exp_fun(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    the_fun: fun >>
    (Expression(pos, _Expression::Fun(the_fun.0, the_fun.1)))
));

named!(exp_array(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    arr: delimited!(
        lbracket,
        separated_list!(comma, exp),
        rbracket
    ) >>
    (Expression(pos, _Expression::Array(arr)))
));

// 1300 is the precedence level
// `field access`
named!(exp_binop_1300(Span) -> Expression, do_parse!(expr: non_leftrecursive_exp >> (expr)));

// 1200 is the precedence level
// `call, index`
named!(exp_binop_1200(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_1300 >>
    fold: fold_many0!(
        delimited!(
            lparen,
            separated_list!(comma, exp),
            rparen
        ),
        first,
        |acc, args| Expression(pos, _Expression::Invocation(Box::new(acc), args))
    ) >>
    (fold)
));

// 1100 is the precedence level
// `::`
named!(exp_binop_1100(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_1200 >>
    fold: fold_many0!(
        do_parse!(
            coloncolon >>
            ident: id >>
            args: delimited!(
                lparen,
                separated_list!(comma, exp),
                rparen
            ) >>
            ((ident, args))
        ),
        first,
        |acc, (ident, args)| Expression(pos, _Expression::Method(Box::new(acc), ident, args))
    ) >>
    (fold)
));

// 1000 is the precedence level
// `?`
named!(exp_binop_1000(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_1100 >>
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

// 900 is the precedence level
// `-, !` (unary)
named!(exp_binop_900(Span) -> Expression, do_parse!(expr: exp_binop_1000 >> (expr)));

// 800 is the precedence level
// `*, /, %`
named!(exp_binop_800(Span) -> Expression, do_parse!(expr: exp_binop_900 >> (expr)));

// 700 is the precedence level
// `+, -` (binary operators)
named!(exp_binop_700(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_800 >>
    fold: fold_many0!(
        do_parse!(
            op: alt!(
                value!(BinOp::Subtract, minus)
            ) >>
            expr: exp_binop_800 >>
            (op, expr)
        ),
        first,
        |acc, (op, rhs)| Expression(pos, _Expression::BinOp(Box::new(acc), op, Box::new(rhs)))
    ) >>
    (fold)
));

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
named!(exp_binop_200(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_300 >>
    fold: fold_many0!(
        do_parse!(
            op: alt!(
                value!(BinOp::Eq, eq)
            ) >>
            expr: exp_binop_300 >>
            (op, expr)
        ),
        first,
        |acc, (op, rhs)| Expression(pos, _Expression::BinOp(Box::new(acc), op, Box::new(rhs)))
    ) >>
    (fold)
));

// 100 is the precedence level
// `&&`
named!(exp_binop_100(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
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
    exp_fun |
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
    exp_blocky |
    exp_array
));

// This is the left-recursive expression of the lowest precedence level
// `||`
named!(exp(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
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
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("return") >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Return(expr)))
));

named!(stmt_break(Span) -> Statement, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("break") >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Break(expr)))
));

named!(stmt_throw(Span) -> Statement, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("throw") >>
    expr: map!(opt!(exp), |maybe_exp| maybe_exp.unwrap_or(Expression::nil())) >>
    (Statement(pos, _Statement::Throw(expr)))
));

named!(stmt_let(Span) -> Statement, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("let") >>
    pat: binder_pat >>
    assign >>
    expr: exp >>
    (Statement(pos, _Statement::Let(pat, expr)))
));

named!(stmt_assign(Span) -> Statement, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    the_id: id >>
    assign >>
    expr: exp >>
    ws0 >>
    (Statement(pos, _Statement::Assign(the_id, expr)))
));

named!(stmt_rec(Span) -> Statement, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("rec") >>
    defs: alt!(
        do_parse!(
            the_id: id >>
            assign >>
            the_fun: fun >>
            (vec![(the_id, the_fun.0, the_fun.1)])
        ) |
        delimited!(
            lbrace,
            separated_list!(
                semi,
                do_parse!(
                    the_id: id >>
                    assign >>
                    the_fun: fun >>
                    (the_id, the_fun.0, the_fun.1)
                )
            ),
            rbrace
        )
    ) >>
    (Statement(pos, _Statement::Rec(defs)))
));

named!(stmt(Span) -> Statement, alt!(
    stmt_assign |
    stmt_exp |
    stmt_return |
    stmt_break |
    stmt_throw |
    stmt_let |
    stmt_rec
));

named!(stmts0(Span) -> Vec<Statement>, separated_list!(semi, stmt));

named!(block(Span) -> Vec<Statement>, delimited!(lbrace, stmts0, rbrace));

named!(pattern_id(Span) -> (Id, bool), do_parse!(
    mutable: map!(opt!(kw!("mut")), |maybe| maybe.is_some()) >>
    binder: id >>
    ((binder, mutable))
));

named!(binder_id(Span) -> BinderPattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    pat: map!(pattern_id, |(binder, mutable)| _BinderPattern::Id(binder, mutable)) >>
    (BinderPattern(pos, pat))
));

named!(binder_blank(Span) -> BinderPattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    pat: value!(_BinderPattern::Blank, blank) >>
    (BinderPattern(pos, pat))
));

named!(binder_outer_array(Span) -> BinderPattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    tmp: alt!(
        do_parse!(
            pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
            lbracket >>
            rbracket >>
            (OuterArrayPattern(pos, _OuterArrayPattern::Closed(vec![])))
        ) |
        delimited!(
            lbracket,
            outer_array_inners,
            rbracket
        )
    ) >>
    (BinderPattern(pos, _BinderPattern::Array(tmp)))
));

named!(outer_array_inners(Span) -> OuterArrayPattern, alt!(
    do_parse!(
        pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
        remaining: array_pattern_remaining >>
        (OuterArrayPattern(pos, outer_array_pattern(vec![], Some(remaining))))
    ) |
    do_parse!(
       pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
       inners: separated_nonempty_list!(comma, do_parse!(
           p: array_pattern >>
           not!(dots) >>
           (p)
       )) >>
       remaining: opt!(do_parse!(
           comma >>
           remaining: array_pattern_remaining >>
           (remaining)
       )) >>
       (OuterArrayPattern(pos, outer_array_pattern(inners, remaining)))
   )
));

named!(array_pattern(Span) -> ArrayPattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    ret: alt!(
        do_parse!(
            id: pattern_id >>
            qm >>
            (_ArrayPattern::QM(id.0, id.1))
        ) |
        map!(binder_pat, _ArrayPattern::Regular)
    ) >>
    (ArrayPattern(pos, ret))
));

enum ArrayRemaining {
    Anon,
    Named(Id, bool),
}

named!(array_pattern_remaining(Span) -> ArrayRemaining, alt!(
    do_parse!(
        id: pattern_id >>
        dots >>
        (ArrayRemaining::Named(id.0, id.1))
    ) |
    value!(ArrayRemaining::Anon, dots)
));

fn outer_array_pattern(inners: Vec<ArrayPattern>, remaining: Option<ArrayRemaining>) -> _OuterArrayPattern {
    match remaining {
        None => _OuterArrayPattern::Closed(inners),
        Some(ArrayRemaining::Anon) => _OuterArrayPattern::Open(inners),
        Some(ArrayRemaining::Named(id, mutable)) => _OuterArrayPattern::OpenNamed(inners, id, mutable),
    }
}

named!(binder_pat(Span) -> BinderPattern, alt!(
    binder_id |
    binder_blank |
    binder_outer_array
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
