// Convert well-formed pavo source code into a syntax tree.
//
// The parsers consume all trailing whitespace, but do not skip over leading whitespace.

use failure_derive::Fail;
use nom::{
    {line_ending, not_line_ending, multispace1, eof},
    {value, tag, take_while1, one_of, is_a},
    {do_parse, alt, many0, many1, opt, fold_many0, many_m_n},
    {delimited, separated_nonempty_list, separated_list},
    {named, not, map, try_parse, call},
    types::CompleteStr, IResult, Err, Context, ErrorKind,
};
use nom_locate::{LocatedSpan, position};

use crate::syntax::{
    Id,
    Expression, _Expression, BinOp,
    Statement, _Statement,
    Patterns,
    Pattern, _Pattern,
    ArrayPattern, ArrayPatternOptionals,
};
use crate::util::SrcLocation;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

// Same as separated_list, but allows a trailing separator.
macro_rules! separated_list_trail(
    ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => ({
        do_parse!(
            $i,
            ret: separated_list!($sep!($($args)*), $submac!($($args2)*)) >>
            opt!($sep!($($args)*)) >>
            (ret)
        )
    });
    ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
        separated_list_trail!($i, $submac!($($args)*), call!($g));
    );
    ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
        separated_list_trail!($i, call!($f), $submac!($($args)*));
    );
    ($i:expr, $f:expr, $g:expr) => (
        separated_list_trail!($i, call!($f), call!($g));
    );
);

// Same as separated_nonempty_list, but allows a trailing separator.
macro_rules! separated_nonempty_list_trail(
    ($i:expr, $sep:ident!( $($args:tt)* ), $submac:ident!( $($args2:tt)* )) => ({
        do_parse!(
            $i,
            ret: separated_nonempty_list!($sep!($($args)*), $submac!($($args2)*)) >>
            opt!($sep!($($args)*)) >>
            (ret)
        )
    });
    ($i:expr, $submac:ident!( $($args:tt)* ), $g:expr) => (
        separated_separated_nonempty_list_trail!($i, $submac!($($args)*), call!($g));
    );
    ($i:expr, $f:expr, $submac:ident!( $($args:tt)* )) => (
        separated_nonempty_list_trail!($i, call!($f), $submac!($($args)*));
    );
    ($i:expr, $f:expr, $g:expr) => (
        separated_nonempty_list_trail!($i, call!($f), call!($g));
    );
);

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
named!(assign(Span) -> (), do_parse!(tag!("=") >> ws0 >> (())));
named!(qm(Span) -> (), do_parse!(tag!("?") >> ws0 >> (())));
named!(comma(Span) -> (), do_parse!(tag!(",") >> ws0 >> (())));
named!(coloncolon(Span) -> (), do_parse!(tag!("::") >> ws0 >> (())));
named!(eq(Span) -> (), do_parse!(tag!("==") >> ws0 >> (())));
named!(dots(Span) -> (), do_parse!(tag!("...") >> ws0 >> (())));
named!(arrow(Span) -> (), do_parse!(tag!("->") >> ws0 >> (())));
named!(fat_arrow(Span) -> (), do_parse!(tag!("=>") >> ws0 >> (())));
named!(pipe(Span) -> (), do_parse!(tag!("|") >> ws0 >> (())));
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
    id == "async" || id == "await" || id == "for" || id == "let" || id == "rec" || id == "_"
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
    let (i, (pos, digits, is_negative)) = try_parse!(i, do_parse!(
        pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
        is_negative: map!(opt!(tag!("-")), |tmp| tmp.is_some()) >>
        tag!("0x") >>
        digits: is_a!("0123456789abcdefABCDEF_") >>
        ws0 >>
        ((pos, digits, is_negative))
    ));

    let raw = std::iter::once(if is_negative { '-' } else { '+' }).chain(
        digits.fragment.0.chars().filter(|ch| *ch != '_')
    ).collect::<String>();

    match i64::from_str_radix(
        &raw,
        16
    ) {
        Ok(n) => Ok((i, (pos, n))),
        Err(_) => Err(Err::Error(Context::Code(i, ErrorKind::Custom(1)))),
    }
}

fn dec_int<'a>(i: Span<'a>) -> IResult<Span<'a>, (SrcLocation, i64)> {
    let (i, (pos, digits, is_negative)) = try_parse!(i, do_parse!(
        pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
        is_negative: map!(opt!(tag!("-")), |tmp| tmp.is_some()) >>
        digits: is_a!("0123456789_") >>
        ws0 >>
        ((pos, digits, is_negative))
    ));

    let raw = std::iter::once(if is_negative { '-' } else { '+' }).chain(
        digits.fragment.0.chars().filter(|ch| *ch != '_')
    ).collect::<String>();

    match i64::from_str_radix(
        &raw,
        10
    ) {
        Ok(n) => Ok((i, (pos, n))),
        Err(_) => Err(Err::Error(Context::Code(i, ErrorKind::Custom(2)))),
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
    else_block: opt!(do_parse!(
            kw!("else") >>
            else_block: alt!(
                block |
                map!(exp_blocky, |e| {
                    vec![Statement(e.0, _Statement::Expression(e))]
                })
            ) >>
            (else_block)
        )) >>
    (Expression(pos, _Expression::If(cond, if_block, else_block)))
));

named!(exp_while(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("while") >>
    cond: map!(exp, Box::new) >>
    loop_block: block >>
    (Expression(pos, _Expression::While(cond, loop_block)))
));

named!(exp_case(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("case") >>
    matchee: map!(exp, Box::new) >>
    lbrace >>
    arms: separated_list_trail!(semi, do_parse!(
        pats: patterns >>
        fat_arrow >>
        the_block: alt!(
            block |
            map!(exp_blocky, |e| {
                vec![Statement(e.0, _Statement::Expression(e))]
            })
        ) >>
        ((pats, the_block))
    )) >>
    rbrace >>
    (Expression(pos, _Expression::Case(matchee, arms)))
));

named!(exp_loop(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("loop") >>
    matchee: map!(exp, Box::new) >>
    lbrace >>
    arms: separated_list_trail!(semi, do_parse!(
        pats: patterns >>
        fat_arrow >>
        the_block: alt!(
            block |
            map!(exp_blocky, |e| {
                vec![Statement(e.0, _Statement::Expression(e))]
            })
        ) >>
        ((pats, the_block))
    )) >>
    rbrace >>
    (Expression(pos, _Expression::Loop(matchee, arms)))
));

named!(exp_try(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("try") >>
    try_block: block >>
    kw!("catch") >>
    pats: patterns >>
    catch_block: block >>
    finally_block: opt!(do_parse!(
            kw!("finally") >>
            finally_block: block >>
            (finally_block)
        )) >>
    (Expression(pos, _Expression::Try(try_block, pats, catch_block, finally_block)))
));

// Expressions that can follow an `else` keyword without being enclosed in braces.
named!(exp_blocky(Span) -> Expression, alt!(
    exp_if | exp_while | exp_try | exp_case | exp_loop
));

named!(fun(Span) -> (ArrayPattern, Vec<Statement>), do_parse!(
    args: delimited!(lparen, pattern_array_inners, rparen) >>
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
        separated_list_trail!(comma, exp),
        rbracket
    ) >>
    (Expression(pos, _Expression::Array(arr)))
));

// TODO add index and field access here (which needs left-associative precedence parsing)
named!(method_exp(Span) -> Expression, alt!(
    exp_id
));

// 1300 is the precedence level
// `field access`
named!(exp_binop_1300(Span) -> Expression, do_parse!(expr: non_leftrecursive_exp >> (expr)));

// 1200 is the precedence level
// `::`
named!(exp_binop_1200(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_1300 >>
    fold: fold_many0!(
        do_parse!(
            coloncolon >>
            method: method_exp >>
            args: delimited!(
                lparen,
                separated_list_trail!(comma, exp),
                rparen
            ) >>
            ((method, args))
        ),
        first,
        |acc, (method, args)| Expression(pos, _Expression::Method(Box::new(acc), Box::new(method), args))
    ) >>
    (fold)
));

// 1100 is the precedence level
// `call, index`
named!(exp_binop_1100(Span) -> Expression, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    first: exp_binop_1200 >>
    fold: fold_many0!(
        delimited!(
            lparen,
            separated_list_trail!(comma, exp),
            rparen
        ),
        first,
        |acc, args| Expression(pos, _Expression::Invocation(Box::new(acc), args))
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
// `&` TODO collapes &, ^ and | into one precedence level
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
// TODO remove this
named!(exp_binop_100(Span) -> Expression, do_parse!(expr: exp_binop_200 >> (expr)));

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
            op: alt!(value!(BoolBinOp::And, land) | value!(BoolBinOp::Or, lor)) >>
            expr: exp_binop_100 >>
            ((expr, op))
        ),
        first,
        |acc, (rhs, op)| Expression(pos, match op {
            BoolBinOp::And => _Expression::Land(Box::new(acc), Box::new(rhs)),
            BoolBinOp::Or => _Expression::Lor(Box::new(acc), Box::new(rhs)),
        })
    ) >>
    (fold)
));

enum BoolBinOp {
    And, Or
}

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
    pats: patterns >>
    assign >>
    expr: exp >>
    (Statement(pos, _Statement::Let(pats, expr)))
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
            separated_list_trail!(
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

named!(stmts0(Span) -> Vec<Statement>, separated_list_trail!(semi, stmt));

named!(block(Span) -> Vec<Statement>, delimited!(lbrace, stmts0, rbrace));

named!(pattern_id_raw(Span) -> (Id, bool), do_parse!(
    mutable: map!(opt!(kw!("mut")), |maybe| maybe.is_some()) >>
    binder: id >>
    ((binder, mutable))
));

named!(pattern_id(Span) -> Pattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    pat: map!(pattern_id_raw, |(binder, mutable)| _Pattern::Id(binder, mutable)) >>
    (Pattern(pos, pat))
));

named!(pattern_blank(Span) -> Pattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    pat: value!(_Pattern::Blank, kw!("_")) >>
    (Pattern(pos, pat))
));

named!(pattern_array(Span) -> Pattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    the_arr: delimited!(lbracket, pattern_array_inners, rbracket) >>
    (Pattern(pos, _Pattern::Array(the_arr)))
));

named!(pattern_array_inners(Span) -> ArrayPattern, do_parse!(
    left: separated_list!(comma, pattern) >>
    opts: map!(
        opt!(do_parse!(
            comma >>
            opts: pattern_array_optionals >>
            (opts)
        )),
        |opts| match opts {
            Some(opts) => opts,
            None => ArrayPatternOptionals::empty(),
        }
    ) >>
    right: map!(
        opt!(do_parse!(
            comma >>
            right: separated_list_trail!(comma, pattern) >>
            (right)
        )),
        |right| match right {
            Some(right) => right,
            None => vec![]
        }
    ) >>
    (ArrayPattern(left, opts, right))
));

named!(pattern_array_optionals(Span) -> ArrayPatternOptionals, alt!(
    do_parse!(
        opts: separated_list!(comma, pattern_optional) >>
        spread: opt!(do_parse!(
            comma >>
            spread: pattern_array_spread >>
            (spread)
        )) >>
        opt!(comma) >>
        (ArrayPatternOptionals::Left(opts, spread))
    ) |
    do_parse!(
        spread: opt!(pattern_array_spread) >>
        opts: do_parse!(
            comma >>
            opts: separated_list_trail!(comma, pattern_optional) >>
            (opts)
        ) >>
        (ArrayPatternOptionals::Right(spread, opts))
    )
));

named!(pattern_optional(Span) -> Pattern, do_parse!(
    pat: pattern >>
    qm >>
    (pat)
));

named!(pattern_array_spread(Span) -> Option<(Id, bool)>, alt!(
    value!(None, dots) |
    map!(pattern_id_raw, Some)
));

named!(pattern_nil(Span) -> Pattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    kw!("nil") >>
    (Pattern(pos, _Pattern::Nil))
));

named!(pattern_bool(Span) -> Pattern, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    b: alt!(value!(true, kw!("true")) | value!(false, kw!("false"))) >>
    (Pattern(pos, _Pattern::Bool(b)))
));

named!(pattern_hex_int(Span) -> Pattern, map!(hex_int, |(pos, n)| Pattern(pos, _Pattern::Int(n))));
named!(pattern_dec_int(Span) -> Pattern, map!(dec_int, |(pos, n)| Pattern(pos, _Pattern::Int(n))));

named!(pattern_num(Span) -> Pattern, alt!(
    pattern_hex_int | pattern_dec_int
));

named!(pattern(Span) -> Pattern, alt!(
    pattern_id |
    pattern_blank |
    pattern_nil |
    pattern_bool |
    pattern_num |
    pattern_array
));

named!(patterns(Span) -> Patterns, do_parse!(
    pos: map!(position!(), |span| SrcLocation::from_span(&span)) >>
    pats: separated_nonempty_list_trail!(pipe, pattern) >>
    guard: opt!(do_parse!(
        kw!("if") >>
        expr: exp >>
        (expr)
    )) >>
    (Patterns(pos, pats, guard.map(Box::new)))
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
