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

### Expressions

Expressions can be wrapped in parentheses without changing their semantics. This can be used to override operator precedences.

#### Literals

All literals are expressions.

#### If-Expressions

An if-expression consists of the keyword `if`, followed by a *condition* (an expression), followed by a sequence of statements delimited by curly braces, optionally followed by the keyword `else` and another block of brace-delimited statements. The `else` keyword may also be followed by a *blocky expression* instead (without the need for curly braces). The list of *blocky expressions* is:

- if-expressions

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
