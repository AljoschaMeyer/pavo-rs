use nom::{Err, types::CompleteStr};
use nom_locate::LocatedSpan;

// The types that make up the pavo syntax trees.
mod syntax;
// A parser to turn well-formed source code into a syntax tree.
mod parse;
// Definition of the pavo runtime values.
mod value;
// The context in which a pavo computation is evaluated.
mod context;
// An intermediate representation of pavo code that gets interpreted.
mod ir;

use context::{Computation, Context, PavoResult};

pub fn execute_pavo<'s>(src: &'s str) -> Result<PavoResult, Err<LocatedSpan<CompleteStr<'s>>>> {
    parse::script(LocatedSpan::new(CompleteStr(src)))
        .map(|(_, ast)| {
            let mut cx = Context::new();
            let ir_chunk = ir::ast_to_ir(&ast);
            return ir_chunk.compute(vec![], &mut cx);
        })
}

#[cfg(test)]
mod tests {
    use super::execute_pavo;
    use super::value::Value;

    fn assert_pavo_ok(src: &str, expected: Value) {
        match execute_pavo(src) {
            Err(err) => panic!("Unexpected parser error: {:?}", err),
            Ok(Err(err)) => panic!("Unexpected exception: {:?}", err),
            Ok(Ok(val)) => assert_eq!(val, expected),
        }
    }

    #[test]
    fn test_trivial() {
        assert_pavo_ok("nil", Value::new_nil());
        assert_pavo_ok("nil; (nil); ((nil))", Value::new_nil());
        assert_pavo_ok("// comment\n nil //this comment ends with eof", Value::new_nil());
        assert_pavo_ok("nil//", Value::new_nil());
        assert_pavo_ok("", Value::new_nil());
    }

    #[test]
    fn test_bools() {
        assert_pavo_ok("true", Value::new_bool(true));
        assert_pavo_ok("false", Value::new_bool(false));
    }

    #[test]
    fn test_if() {
        assert_pavo_ok("if true {}", Value::new_nil());
        assert_pavo_ok("if true { false }", Value::new_bool(false));
        assert_pavo_ok("if false { false }", Value::new_nil());
        assert_pavo_ok("if false { false } else { false; true }", Value::new_bool(true));
        assert_pavo_ok("if false { false } else if true { true }", Value::new_bool(true));
        assert_pavo_ok("if if true { false } { false } else { true }", Value::new_bool(true));
    }
}
