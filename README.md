# The Pavo Programming Language

An imperative, dynamically typed, event-loop based programming language. Featuring immutable values and capability-based code loading.

## Values and Types

Pavo is dynamically typed. Variables bindings don't have statically known types, instead all values carry their type with them at runtime. The possible types are:

- `nil`: The unit type.
- `bool`: Either `true` or `false`.
- `function`: A function, or strictly speaking a closure.

### Nil

The `nil` type only holds a single value: `nil` (which is also the literal of the value).

### Bool

The `bool` type holds two values: `true` and `false` (which are also the literals of the values).

### Function

A `function` represents a computation. The function can be applied to some arguments, and either returns a value or throws one.

## Other Toplevel Functions

### Equality and Ordering

TODO words (blocked on: will floats include NaN?, is ordering on ref types deterministic?)

#### `eq(a, b)`

Returns `true` iff `a == b`.

## Syntax and Semantics

Pavo is an imperative language with C-like syntax. *Expressions* are evaluated to values, and *statements* are executed in sequence to perform actions depending on those values. Statements also evaluate to values, those statements that are executed purely for side-effects evaluate to `nil`. A piece of pavo source code is called a *script*. Each script consists of any number of statements, separated by semicolons. Any semicolon-separated sequence of statements evaluates to the value to which the last of those statements evaluated. The empty sequence of statements evaluates to `nil`.

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

The syntax for let statements is `let some_binder_pattern = some_expression`. The let statement evalutes the expression and then binds the identifiers in the binder pattern (see next section) according to the resulting value. The statement itself evaluates to `nil`.

### Binder Patterns

Binder patterns are used to destructure expressions into subcomponents and bind these subcomponents to names. All mechanisms in pavo that introduce bound identifiers (`let` bindings, `catch` clauses and function arguments) do so via patterns.

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

The syntax for try-expressions is `try { statements... } catch binder_pattern { statements...} finally { statements... }`, the `finally { statements... }` part is optional. The expressions starts evaluating the statements in the try-block. If any of them throws, the thrown value is matched against the binder pattern, and then the catch-block is executed. When execution reached the end of either the try-block or the catch-block, execution resumes with the finally-block. If the finally-block was omitted, the expressions behaves as if there was an empty finally-block. If the finally-block is empty, the try-expression evaluates to the result of the try-block if it didn't throw, or the result of the catch-block otherwise. If there is at least one statement in the finally-block, the expression evaluates to the result of the finally-block.

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

All operators in pavo are left-associative. The list of operator precendeces, from higher to lower precedence:

- function invocation (`fun(args)`)
- "method" syntax (`arg1::fun_id(args)`)
- `?`
- `==`
- `&&`
- `||`

For example, `a || b && c` is parsed as `a || (b && c)` (`&&` has higher precedence than `||`), whereas `a || b || c` is parsed as `(a || b) || c` (equal precedence, so it defaults to left-associativity).

##### Function Invocation

An expression followed by an opening paren, followed by any number of expressions, followed by a closing paren is a function invocation. First, the arguments are evaluated from left to right (independent of the OS locale), then the function expression itself is evaluated, and then the arguments are applied to the function.

##### "Method" Syntax

`exp::some_id(args)` is equivalent to `some_id(exp, args)`.

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
