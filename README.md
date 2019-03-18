# The Pavo Programming Language

An imperative, dynamically typed, event-loop based programming language. Featuring immutable values and capability-based code loading.

## Values and Types

Pavo is dynamically typed. Variables bindings don't have statically known types, instead all values carry their type with them at runtime. The possible types are:

- `nil`: The unit type.

### Nil

The `nil` type only holds a single value: `nil` (which is also the literal of the value).

## Statements, Expressions and Execution

Pavo is an imperative language with C-like syntax. *Expressions* are evaluated to values, and *statements* are executed in sequence to perform actions depending on those values. A piece of pavo source code is called a *script*. Each script consists of any number of statements, separated by semicolons.

All expressions are also statements. Expressions can be wrapped in parentheses.

```pavo
// This is a very boring pavo program. Surprisingly enough, it evaluates to `nil`.
nil;
((nil));
(nil)
// Note how the last statement is not terminated by a semicolon.
```
