use failure_derive::Fail;
use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

// The types that make up the pavo syntax trees.
mod syntax;
// A parser to turn well-formed source code into a syntax tree.
mod parse;
// The subset of pavo produced after desugaring.
mod syntax_light;
// Resolves bindings, detects free identifiers and mutability violations.
mod binding_analysis;
// Definition of the pavo runtime values.
mod value;
// The context in which a pavo computation is evaluated.
mod context;
// An intermediate representation of pavo code that gets interpreted.
mod ir;
mod util;
mod builtins;
mod toplevel;
mod gc_foreign;

use binding_analysis::AnalysisError;
use context::{Computation, Context, PavoResult};
use parse::ParseError;

#[derive(PartialEq, Eq, Debug, Clone, Hash, Fail)]
pub enum StaticError {
    #[fail(display = "malformed input file, error during parsing")]
    Parse(#[fail(cause)] ParseError),
    #[fail(display = "error detected during static analysis")]
    Analysis(#[fail(cause)] AnalysisError),
}

impl From<ParseError> for StaticError {
    fn from(err: ParseError) -> Self {
        StaticError::Parse(err)
    }
}

impl From<AnalysisError> for StaticError {
    fn from(err: AnalysisError) -> Self {
        StaticError::Analysis(err)
    }
}

pub fn execute_pavo<'s>(src: &'s str) -> Result<PavoResult, StaticError> {
    let ast = parse::script(LocatedSpan::new(CompleteStr(src)))?;
    let desugared = syntax_light::desugar_statements(ast);
    let analyzed = binding_analysis::analyze_statements(desugared, toplevel::BINDINGS)?;
    let ir_chunk = ir::ast_to_ir(analyzed);
    let main = ir::Closure::from_script_chunk(ir_chunk);

    let mut cx = Context::new();
    return Ok(main.compute(&vec![], &mut cx));
}

#[cfg(test)]
mod tests {
    use super::{execute_pavo, StaticError};
    use super::value::Value;
    use super::binding_analysis::AnalysisError;

    fn assert_pavo_ok(src: &str, expected: Value) {
        match execute_pavo(src) {
            Err(err) => panic!("Unexpected static error: {:?}", err),
            Ok(Err(err)) => panic!("Unexpected runtime error: {:?}", err),
            Ok(Ok(val)) => assert_eq!(val, expected),
        }
    }

    fn assert_pavo_thrown(src: &str, expected: Value) {
        match execute_pavo(src) {
            Err(err) => panic!("Unexpected parser error: {:?}", err),
            Ok(Ok(val)) => panic!("Expected to throw, but returned: {:?}", val),
            Ok(Err(thrown)) => assert_eq!(thrown, expected),
        }
    }

    #[test]
    fn test_nil() {
        assert_pavo_ok("nil", Value::new_nil());
        assert_pavo_ok("nil; (nil); ((nil))", Value::new_nil());
        assert_pavo_ok("# com#ment\n nil #this comment ends with eof", Value::new_nil());
        assert_pavo_ok("nil#", Value::new_nil());
        assert_pavo_ok("", Value::new_nil());
        assert_pavo_ok(";", Value::new_nil());
    }

    #[test]
    fn test_bools() {
        assert_pavo_ok("true", Value::new_bool(true));
        assert_pavo_ok("false", Value::new_bool(false));
        assert_pavo_ok("true; false;", Value::new_bool(false));
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

    #[test]
    fn test_land_and_lor() {
        assert_pavo_ok("true || true", Value::new_bool(true));
        assert_pavo_ok("true || false", Value::new_bool(true));
        assert_pavo_ok("false || true", Value::new_bool(true));
        assert_pavo_ok("false || false", Value::new_bool(false));
        assert_pavo_ok("true && true", Value::new_bool(true));
        assert_pavo_ok("true && false", Value::new_bool(false));
        assert_pavo_ok("false && true", Value::new_bool(false));
        assert_pavo_ok("false && false", Value::new_bool(false));

        assert_pavo_ok("false && false || true", Value::new_bool(true));
        assert_pavo_ok("(false && false) || true", Value::new_bool(true));
        assert_pavo_ok("false && (false || true)", Value::new_bool(false));

        // && and || are short-circuiting
        assert_pavo_ok("false && while true {}", Value::new_bool(false));
        assert_pavo_ok("true || while true {}", Value::new_bool(true));
    }

    #[test]
    fn test_return() {
        assert_pavo_ok("return true; false", Value::new_bool(true));
        assert_pavo_ok("return; false", Value::new_nil());
    }

    #[test]
    fn test_while() {
        assert_pavo_ok("while false {}", Value::new_nil());
        assert_pavo_ok("while false { true }; false", Value::new_bool(false));
        assert_pavo_ok("while true { break false; true }", Value::new_bool(false));
        assert_pavo_ok("
            while true {
                nil;
                while true {
                    nil;
                    break
                };
                break true
            };
            false", Value::new_bool(false));
        assert_pavo_ok("
            let mut x = true;
            while x {
                x = false;
                true
            }", Value::new_bool(true));
    }

    #[test]
    fn test_identifiers() {
        assert_pavo_ok("let x = true; x", Value::new_bool(true));
        assert_pavo_ok("let mut x = true; x = false; x", Value::new_bool(false));
        assert_pavo_ok("
            let mut x = true;
            while x {
                let x = false;
                if x { return false } else { return true }
            };
            false", Value::new_bool(true));
    }

    #[test]
    fn test_static_analysis() {
        match execute_pavo("x").unwrap_err() {
            StaticError::Analysis(AnalysisError::Free(..)) => {},
            _ => panic!(),
        }

        match execute_pavo("x = nil").unwrap_err() {
            StaticError::Analysis(AnalysisError::Free(..)) => {},
            _ => panic!(),
        }

        match execute_pavo("x; let x = nil").unwrap_err() {
            StaticError::Analysis(AnalysisError::Free(..)) => {},
            _ => panic!(),
        }

        match execute_pavo("let x = true; x = false").unwrap_err() {
            StaticError::Analysis(AnalysisError::Immutable(..)) => {},
            _ => panic!(),
        }
    }

    #[test]
    fn test_try_catch_finally() {
        assert_pavo_thrown("throw; false", Value::new_nil());
        assert_pavo_thrown("throw true; false", Value::new_bool(true));
        assert_pavo_ok("try { true } catch _ {}", Value::new_bool(true));
        assert_pavo_ok("try { throw true } catch _ { false }", Value::new_bool(false));
        assert_pavo_ok("try { throw true } catch x { x }", Value::new_bool(true));
        assert_pavo_ok("try { throw true } catch mut x { x = false; x }", Value::new_bool(false));
        assert_pavo_ok("try {} catch x { x }", Value::new_nil());
        assert_pavo_ok("try {} catch x { x } finally { true }", Value::new_bool(true));
        assert_pavo_ok("try { throw false } catch x { x } finally { true }", Value::new_bool(true));
    }

    #[test]
    fn test_questionmark() {
        assert_pavo_thrown("throw true?", Value::new_bool(true));
        assert_pavo_thrown("throw true?; false", Value::new_bool(true));
        assert_pavo_ok("try { if true {throw false}?; true } catch _ {false}", Value::new_bool(true));
        assert_pavo_ok("true && if true {throw true; true}?", Value::new_bool(false));
        assert_pavo_ok("true???", Value::new_bool(true));
        assert_pavo_ok("false???; true", Value::new_bool(true));
    }

    #[test]
    fn test_invocation() {
        assert_pavo_thrown("false(true, nil, false,)", Value::new_nil());
        assert_pavo_thrown("false()", Value::new_nil());
    }

    #[test]
    fn test_method() {
        assert_pavo_thrown("let x = false; true::x(nil, true)", Value::new_nil());
        assert_pavo_thrown("let x = false; true::x()", Value::new_nil());
    }

    #[test]
    fn test_binops() {
        assert_pavo_ok("nil == false", Value::new_bool(false));
        assert_pavo_ok("false == false", Value::new_bool(true));
    }

    #[test]
    fn test_builtins() {
        assert_pavo_ok("eq(true, true)", Value::new_bool(true));
        assert_pavo_ok("eq(eq, eq)", Value::new_bool(true));
        assert_pavo_ok("eq(true, false)", Value::new_bool(false));
        assert_pavo_ok("eq(eq, eq, false)", Value::new_bool(true));
        assert_pavo_ok("eq(nil, false, false)", Value::new_bool(false));
        assert_pavo_ok("eq(false)", Value::new_bool(false));
        assert_pavo_ok("eq(nil)", Value::new_bool(true));
        assert_pavo_ok("eq()", Value::new_bool(true));
    }

    #[test]
    fn test_arrays() {
        assert_pavo_ok("[] == []", Value::new_bool(true));
        assert_pavo_ok("[[nil], true] == [[nil], true]", Value::new_bool(true));
    }

    #[test]
    fn test_array_patterns() {
        assert_pavo_ok("let [] = []", Value::new_nil());
        assert_pavo_ok("let [a] = [true]; a", Value::new_bool(true));
        assert_pavo_ok("let [a, b?] = [true]; a", Value::new_bool(true));
        assert_pavo_ok("let [a, b?] = [true, false]; b", Value::new_bool(false));
        assert_pavo_ok("let [a, b?,] = [true]; b", Value::new_nil());
        assert_pavo_ok("let [a, mut b?,] = [true]; b = a; b", Value::new_bool(true));
        assert_pavo_ok("let [a, ...,] = [true]; a", Value::new_bool(true));
        assert_pavo_ok("let [a, ...] = [true, nil, nil]; a", Value::new_bool(true));
        assert_pavo_ok("let [a, b...,] = [false]; b == []", Value::new_bool(true));
        assert_pavo_ok("let [a, b...] = [false, false]; b == [false]", Value::new_bool(true));
        assert_pavo_ok("let [a, b...] = [false, false, false]; b == [false, false]", Value::new_bool(true));
        assert_pavo_ok("let [a, mut b...] = [false]; b = b == []; b", Value::new_bool(true));
        assert_pavo_ok("let [...] = []; true", Value::new_bool(true));
        assert_pavo_ok("let [a, b?, c...] = [false]; a", Value::new_bool(false));
        assert_pavo_ok("let [[a]] = [[true]]; a", Value::new_bool(true));
        assert_pavo_ok("let [a] = [[true]]; a == [true]", Value::new_bool(true));

        assert_pavo_thrown("let [] = false", Value::new_nil());
        assert_pavo_thrown("let [] = [false]", Value::new_nil());
        assert_pavo_thrown("let [a,] = [false, false]", Value::new_nil());
        assert_pavo_thrown("let [...] = false", Value::new_nil());
        assert_pavo_thrown("let [a...] = false", Value::new_nil());
        assert_pavo_thrown("let [a, b, c...] = [false]", Value::new_nil());
        assert_pavo_thrown("let [[]] = [false]", Value::new_nil());
    }

    #[test]
    fn test_funs() {
        assert_pavo_ok("() -> {} == () -> {}", Value::new_bool(false));
        assert_pavo_ok("let a = () -> {}; a == a", Value::new_bool(true));

        assert_pavo_ok("() -> {}()", Value::new_nil());
        assert_pavo_ok("() -> {true}()", Value::new_bool(true));
        assert_pavo_thrown("() -> {}(nil)", Value::new_nil());
        assert_pavo_ok("(...) -> {true}(nil, false)", Value::new_bool(true));
        assert_pavo_ok("(a, mut b, c...) -> {
          b = false;
          a == b && c == [nil, false]
        }(false, true, nil, false)", Value::new_bool(true));

        assert_pavo_ok("
        let a = true;
        let mut c = false;

        () -> {
          let mut b = nil;

          # This argument shadows the outer `b` defined two lines above, the outer one is never mutated
          let foo = (mut b) -> {
            b = b || a;
            b
          };

          let ret = foo(false); # ret gets set to true
          c = b == nil; # c gets set to true

          ret
        }() && c # evaluates to true", Value::new_bool(true));
    }

    #[test]
    fn test_ints() {
        assert_pavo_ok("0x11 == 17", Value::new_bool(true));
        assert_pavo_ok("3 - 7", Value::new_int(-4));
        assert_pavo_ok("100 - 10 - 1 == 89", Value::new_bool(true));
        assert_pavo_ok("0x__1_1__ == 1__7_", Value::new_bool(true));
    }

    #[test]
    fn test_rec() {
        assert_pavo_ok("rec check_positive = (n) -> {
            if n == 0 {
                true
            } else {
                check_positive(n - 1)
            }
        };
        check_positive(49999)", Value::new_bool(true));

        assert_pavo_ok("rec {
            check_even = (n) -> {
                if n == 0 {
                    true
                } else {
                    check_odd(n - 1)
                }
            };

            check_odd = (n) -> {
                if n == 0 {
                    false
                } else {
                    check_even(n - 1)
                }
            }
        };
        check_odd(49999) && check_even(50000)", Value::new_bool(true));

        assert_pavo_ok("rec {}", Value::new_nil());
    }
}
