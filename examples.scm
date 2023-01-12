(load "lambdacalc.scm")

(display "Example 1")
(newline)

(display
  (evaluate
    (lambda-cfg
      (lex "let double = (n . n + n), (double 5);"))))
(newline)
