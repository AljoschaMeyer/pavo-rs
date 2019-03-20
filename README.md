# The Pavo Programming Language

An imperative, dynamically typed, event-loop based programming language. Featuring immutable values and capability-based code loading.

## Values and Types

Pavo is dynamically typed. Variables bindings don't have statically known types, instead all values carry their type with them at runtime. The possible types are:

- `nil`: The unit type.
- `bool`: Either `true` or `false`.

### Nil

The `nil` type only holds a single value: `nil` (which is also the literal of the value).

### Bool

The `bool` type holds two values: `true` and `false` (which are also the literals of the values).

## Statements, Expressions and Execution

Pavo is an imperative language with C-like syntax. *Expressions* are evaluated to values, and *statements* are executed in sequence to perform actions depending on those values. Statements also evaluate to values, those statements that are executed purely for side-effects evaluate to `nil`. A piece of pavo source code is called a *script*. Each script consists of any number of statements, separated by semicolons. Any semicolon-separated sequence of statements evaluates to the value to which the last of those statements evaluated. The empty sequence of statements evaluates to `nil`.

### Statements

All expressions are also statements.

```pavo
// This is a very boring pavo program. Surprisingly enough, it evaluates to `nil`.
nil;
((nil));
(nil)
// Note how the last statement is not terminated by a semicolon.
```

#### Return

The `return x` statement exits the current function, making it evaluate to `x`. If the expression `x` is omitted, the function returns `nil`. This statement can also be used in a top-level script, ending its execution.

#### Break

The `break x` statement leaves the body of the enclosing loop, making it evaluate to `x`. If the expression `x` is omitted, it evaluates to `nil`. If there is no enclosing loop, `break x` is equivalent to `return x`.

### Expressions

Expressions can be wrapped in parentheses without changing their semantics. This can be used to override operator precedences.

#### Literals

All literals are expressions.

#### If-Expressions

An if-expression consists of the keyword `if`, followed by a *condition* (an expression), followed by a sequence of statements delimited by curly braces, optionally followed by the keyword `else` and another block of brace-delimited statements. The `else` keyword may also be followed by a *blocky expression* instead (without the need for curly braces). The list of *blocky expressions* is:

- if-expressions
- while-expressions

Evaluation of an if-expression begins by evaluating the *condition*. If it is *truthy* (neither `nil` nor `false`), then evaluate the following block. If the condition is not truthy, then evaluate the else-block (or the else-blocky-expression) instead. If the condition is not truthy and there is no else-block, the if-expression evaluates to `nil`.

```pavo
// evaluates to nil
if true {
  if false {}
} else if true {
  false;
  true
}
```

#### While-Expressions

A while-expression consists of the keyword `while`, followed by a *condition* (an expression), followed by a sequence of statements delimited by curly braces.

Evaluation of a while-expression begins by evaluating the *condition*. If it is *truthy* (neither `nil` nor `false`), then evaluate the following block. This process is repeated until the condition becomes falsey (`nil` or `false`). The while-expression evaluates to the value of the last statement of the body in the last evaluation of the body. If the body is evaluated zero times, the while-expression evaluates to `nil`.

#### Operators

All operators in pavo are left-associative. The list of operator precendeces, from higher to lower precedence:

- `&&`
- `||`

For example, `a || b && c` is parsed as `a || (b && c)` (`&&` has higher precedence than `||`), whereas `a || b || c` is parsed as `(a || b) || c` (equal precedence, so it defaults to left-associativity).

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
