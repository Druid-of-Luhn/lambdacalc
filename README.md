# LambdaCalc

A basic extension of lambda calculus supporting assignments and consecutive expressions implemented in Scheme.

Parsing is performed using a CFG macro to enable writing a CFG in BNF-like form, which generates a shift-reduce parser.

Evaluation is performed using a pattern matching macro to enable dispatch based on AST node type and structure. Alpha and beta reduction are used up to the evaluation of binary operators, while symbols may need to be looked up in a global scope.

The "examples.scm" file contains a simple example demonstrating assignment of a function to a symbol and the use of that function.

```scheme
(load "lambdacalc.scm")

(evaluate
  (lambda-cfg
    (lex "let double = (n . n + n), (double 5);"))))
```
