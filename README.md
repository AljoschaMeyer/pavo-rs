# The Pavo Programming Language

An imperative, dynamically typed, event-loop based programming language. Featuring immutable values and capability-based code loading.

## Values and Types

Pavo is dynamically typed. Variables bindings don't have statically known types, instead all values carry their type with them at runtime. The possible types are:

- `nil`: The unit type.
- `bool`: Either `true` or `false`.
- `int`: An integer between `- 2^63` and `2^63 - 1`.
- `array`: An ordered sequence of values.
- `function`: A function, or strictly speaking a closure.

### Nil

The `nil` type only holds a single value: `nil` (which is also the literal of the value).

### Bool

The `bool` type holds two values: `true` and `false` (which are also the literals of the values).

### Int

Integers are 64 bit signed integers, capable of representing all values between `- 2^63` and `2^63 - 1` (inclusive). Integer literals can be written in two forms: Either as a sequence of decimal digits and underscores, or as the prefix `0x` followed by a sequence of hexadecimal digits (both lower case and upper case letters are fine) and underscores. Underscores are ignored when converting into a number, they only serve as a readability aid. An integer literal can not begin with an underscore - such a construct would be parsed as an identifier instead.

Both form of integer literals can be prexifed with a minus (`-`) to yield a negative integer. If the number denoted by the literal is not between `- 2^63` and `2^63 - 1` (inclusive), it is a parser error.

### Arrays

An `array` is an immutable, ordered sequence of pavo values, potentially heterogenous. Array literals are written as `[]`, `[foo]`, `[foo, bar, ...]`.

### Function

A `function` represents a computation. The function can be applied to some arguments, and either returns a value or throws one.

Functions use reference identity for equality comparisons, not structural equivalence:

```pavo
() -> {} == () -> {}; # false, these are two distinct function values at different memory addresses

let a = () -> {};
a == a; # true, both are the same object in memory
a == () -> {} # false again, the right side is a new, different value
```

Function literals are written as `(args) -> { statements }`, where `args` is an array pattern without the outer brackets. When a function is applied to a list of arguments, this list is (conceptually) converted into an array and then matched against the argument array pattern. So the argument list can use all the neat features of patterns. A slightly unusual consequence of this: Unless the args pattern ends with `...`, calling the function with too many arguments results in a runtime error.

```pavo
() -> {}(); # works, evaluates to nil (which is the default for empty blocks)
() -> {}(nil); # throws, too many arguments (the corresponding array pattern would be `[]`, which doesn't match the argument list `[nil]`)
(...) -> {}(nil, false); # yup, works
(a, mut b, c...) -> {
  b = false;
  a == b && c == [nil, false]
}(false, true, nil, false) # evaluates to true
```

Function literals create lexically scoped *closures*, they capture the environment in which they are contained.

```pavo
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
}() && c # evaluates to true
```

## Syntax and Semantics

Pavo is an imperative language with C-like syntax. *Expressions* are evaluated to values, and *statements* are executed in sequence to perform actions depending on those values. Statements also evaluate to values, those statements that are executed purely for side-effects evaluate to `nil`. A piece of pavo source code is called a *script*. Each script consists of any number of statements, separated by semicolons. Any semicolon-separated sequence of statements evaluates to the value to which the last of those statements evaluated. The empty sequence of statements evaluates to `nil`. All sequences with separators may optionally have a trailing separator, e.g. both `{nil; nil}` and `{nil; nil;}` are valid blocks (and so are both `{}` and `{;}`).

### Keywords

The following words have special meaning in the language:

```ascii
nil, true, false, if, else, return, break, while, let, mut, loop, case, throw, try, catch, finally, async, await, for, nan, inf
```

### Identifiers

An identifier consists of one to 255 alphanumeric/underscore ascii characters. It must not begin with a number, and the underscore alone is not an identifier. Additionally, an identifier can not be equal to a keyword. Free identifiers are syntax errors, bound identifiers evaluate to whatever value they are currently bound to.

### Statements

All expressions are also statements.

```pavo
# This is a very boring pavo program. Surprisingly enough, it evaluates to `nil`.
nil;
((nil));
(nil)
# Note how the last statement is not terminated by a semicolon.
```

#### Return

The `return x` statement exits the current function, making it evaluate to `x`. If the expression `x` is omitted, the function returns `nil`. This statement can also be used in a top-level script, ending its execution.

#### Break

The `break x` statement leaves the body of the enclosing loop, making it evaluate to `x`. If the expression `x` is omitted, it evaluates to `nil`. If there is no enclosing loop, `break x` is equivalent to `return x`.

#### Throw

The `throw x` statement throws the expression `x`. If the expression `x` is omitted, it throws `nil`. A thrown value is propagated through the call stack until it is caught in a try-catch expression. If the value is not caught at all, execution of the pavo script ends.

#### Assign

The syntax for assignment is `some_identifier = some_expression`. The identifier must be bound by a mutable binding, anything else (free identifier or immutable binding) is a syntax error. The assign statement evaluates the expression and rebinds the identifier to the resulting value. The statement itself evaluates to `nil`.

#### Let

The syntax for let statements is `let some_binder_patterns = some_expression`. The let statement evaluates the expression and then binds the identifiers in the binder patterns according to the resulting value. The statement itself evaluates to `nil`.

#### Rec

Let statements are not suitable for defining recursive functions. For those, use the `rec` statement, whose syntax is either `rec some_id = (some_args) -> {}` for a single recursive function, or `rec { first_id = (first_args) -> {}; second_id = (second_args) -> {}; ...}` for mutually recursive functions. Unlike a `let` binding, the identifiers of the functions are bound inside the function bodies. The statement itself evaluates to `nil`.

Pavo has (mutually recursive) tail-call optimization, so the following examples work just fine (as opposed to overflowing the call stack in a language without tco):

```pavo
rec check_positive = (n) -> {
    if n == 0 {
        true
    } else {
        check_positive(n - 1)
    }
};
check_positive(49999) # true
```

```pavo
rec {
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
check_odd(49999) && check_even(50000) # true
```

### Binder Patterns

Binder patterns are used to destructure expressions into subcomponents and bind these subcomponents to names. All mechanisms in pavo that introduce bound identifiers (`let` bindings, `catch` clauses, `case` and `loop` expressions, and function arguments) do so via patterns.

No single pattern may bind the same identifier multiple times, so e.g `let [a, a] = nil` would be a syntax error.

#### Blank Pattern

The underscore `_` (which is *not* a valid identifier) pattern ignores matches any value, but does not bind it to a name.

#### Id Pattern

An identifier matches any value, the identifier is then bound to the value. This creates an immutable binding, the identifier can not be reassigned to. It is however perfectly valid to subsequently shadow the binding. Bindings are lexically scoped, each pair of curly braces introduces a new scope.

```pavo
let x = true;
x = false # Syntax error, can not assign to an immutable binding.
```

```pavo
let x = true;
let x = false # This is fine, it creates a new binding that shadows the old one.
```

A mutable binding is created by preceding the identifier with the `mut` keyword.

```pavo
let mut x = true;
x = false;
x # evaluates to `false`
```

```pavo
let mut x = true;
if x {
  let x = false; # shadows the outer x (and is immutable, so we can't reassign in this scope)
  if x {
    # not reached
  } else {
    let mut x = true; # shadowing again, now we can mutate
    x = false; # this only mutates the inner `x`
  }
};
x # still `true`, we never mutated the outermost binding
```

#### Nil Pattern

The nil pattern `nil` matches only the value `nil`.

#### Bool Patterns

The bool patterns `true` and `false` matches only the values `true` and `false` respectively.

#### Int Patterns

Integer patterns use the same syntax as integer literals (including the optional leading minus sign and the ability to write in hexadecimal). They match the int value denothed by the literal.

#### Array Pattern

An array pattern looks like an array, except it lists patterns rather than expressions. To match the pattern, the length of the array must equal the length of the pattern.

```pavo
let [mut a, b, _] = [true, false, true]; # now a == true and b == false
let [a, b] = [true]; # this errors, length mismatch
let [a] = [true, false] # another length mismatch, another error
let [] = [] # this works
let [a] = true # if the expresson does not evaluate to an array, it errors
```

Id patterns inside an array pattern can be made optional by suffixing them with a `?`. If the array value is too short, the pattern still matches and the identifier is bound to `nil`.

```pavo
let [a, b?] = [true] # a == true, b == nil
let [a, b?, c] = [true] # errors, length mismatch
let [a, b?] = [true, false, true] # errors, length mismatch
```

If you only care about the first values of an array but not about any remaining ones, you can use `...` as the last part of an array pattern.

```pavo
let [a, ...] = [true, false, nil] # a == true
let [a, ...] = [true] # a == true
let [a, ...] = [] # errors, length mismtach
let [a?, ...] = [] # works, a == nil
```

Finally, you can bind the remaining values to a name:

```pavo
let [a, b...] = [true, false, nil] # a == true and b == [false, nil]
let [a, mut b...] = [true, false] # a == true and b == [false]
let [a, b...] = [true] # a == true and b == []
let [a, b?, c...] = [true] # a == true and b == nil and c == []
let [a?, b...] = [] # a == nil and b == []
let [a?, b...] = [true] # a == true and b == []
```

### Pattern Lists and Guards

`let` bindings, `catch` clauses, `case` expressions and `loop` expressions actually accept a list of one or more patterns, separated by `|`, optionally followed by a guard `if guard_exp`. The pattern list matches if any of its patterns matches, and if the `guard_exp` evaluates truthy. In a pattern list, all patterns must bind the same set of identifiers with the same mutabilities.

```pavo
let [x] | x = false; # binds x to false
let y if false = true; # throws since the guard evaluates falsey
let [x] | x if x = true; # binds x to true, the guard evaluates to true so it works
let [x] | x if x = false; # throws since the guard evaluates falsey
```

```pavo
let x | y = nil; # this does not compile, all patterns must bind the same names
let x | mut x = nil; # this does not compile, all names must be bound with the same mutability
```

### Expressions

Expressions can be wrapped in parentheses without changing their semantics. This can be used to override operator precedences.

#### Literals

All literals are expressions.

#### Identifiers

An identifier consists of one to 255 alphanumeric/underscore ascii characters. It must not begin with a number, and the underscore alone is not an identifier. Free identifiers are syntax errors, bound identifiers evaluate to whatever value they are currently bound to.

```pavo
# This is a syntax error since x is free (it has not been explicitly
# defined and is not part of the top-level bindings provided by pavo)
x
```

```pavo
let x = false;
let x = true;
x # evaluates to true
```

#### If

An if-expression consists of the keyword `if`, followed by a *condition* (an expression), followed by a sequence of statements delimited by curly braces, optionally followed by the keyword `else` and another block of brace-delimited statements. The `else` keyword may also be followed by a *blocky expression* instead (without the need for curly braces). The list of *blocky expressions* is:

- if-expressions
- while-expressions
- try-expressions

Evaluation of an if-expression begins by evaluating the *condition*. If it is *truthy* (neither `nil` nor `false`), then evaluate the following block. If the condition is not truthy, then evaluate the else-block (or the else-blocky-expression) instead. If the condition is not truthy and there is no else-block, the if-expression evaluates to `nil`.

```pavo
# evaluates to nil
if true {
  if false {}
} else if true {
  false;
  true
}
```

#### While

A while-expression consists of the keyword `while`, followed by a *condition* (an expression), followed by a sequence of statements delimited by curly braces.

Evaluation of a while-expression begins by evaluating the *condition*. If it is *truthy* (neither `nil` nor `false`), then evaluate the following block. This process is repeated until the condition becomes falsey (`nil` or `false`). The while-expression evaluates to the value of the last statement of the body in the last evaluation of the body. If the body is evaluated zero times, the while-expression evaluates to `nil`.

#### Try

The syntax for try-expressions is `try { statements... } catch binder_pattern { statements...} finally { statements... }`, the `finally { statements... }` part is optional. The expressions starts evaluating the statements in the try-block. If any of them throws, the thrown value is matched against the binder pattern, and then the catch-block is executed. When execution reached the end of either the try-block or the catch-block, execution resumes with the finally-block if present. The expression evaluates to the same value as the last executed block.

```pavo
try {
  throw true
} catch _ {
  false
}
# evaluates to false
```
```pavo
try {
  throw false
} catch x {
  x
} finally {
  true
}
# evaluates to true
```

#### Operators

All operators in pavo are left-associative. The list of operator precendeces, from higher to lower precedence (operators in the same row have equal precedence):

- function invocation (`fun(args)`)
- "method" syntax (`arg1::method_exp(args)`)
- `?`
- `==`
- `&&`, `||`

For example, `a || b == c` is parsed as `a || (b == c)` (`==` has higher precedence than `||`), whereas `a || b && c` is parsed as `(a || b) && c` (equal precedence, so it defaults to left-associativity).

##### Function Invocation

An expression followed by an opening paren, followed by any number of expressions, followed by a closing paren is a function invocation. First, the arguments are evaluated from left to right (independent of the OS locale), then the function expression itself is evaluated, and then the arguments are applied to the function.

##### "Method" Syntax

`exp::method_exp(args)` is equivalent to `method_exp(exp, args)`. The `method_exp` can not be an arbitrary expressions, as that would lead to syntactic ambiguatity. `method_exp` must be one of:

- any expression that is not left-recursive
- a field access on a method_exp
- indexing into a method_exp

```pavo
# The following examples are valid:
a::b();
a::b.c[d](e, f);

# These are invalid:
a::b::c()(z)
a::b || c(z)

# This one is valid:
a::b(c)(d) # parsed as (a::b(c))(d)
```

##### `?` (Questionmark Operator)

This is an unary postfix operator, `x?` is equivalent to

```pavo
try {
  x
} catch _ {
  nil
}
```

##### `==` (Equality)

`a == b` evaluates to the same result as `eq(a, b)`.

##### `&&` (Logical And)

`a && b` is equivalent to

```pavo
if a {
  if b {
    true
  } else {
    false
  }
} else {
  false
}
```

##### `||` (Logical Or)

`a || b` is equivalent to

```pavo
if a {
  true
} else {
  if b {
    true
  } else {
    false
  }
}
```

## Toplevel Values

### Other Toplevel Values

Toplevel values (mostly functions) that are not explicitly tied to any one type. Sorted into some rough categories.

#### Equality and Ordering

TODO words (blocked on: will floats include NaN?, is ordering on ref types deterministic?)

##### `eq(a, b)`

Returns `true` iff `a == b`.
