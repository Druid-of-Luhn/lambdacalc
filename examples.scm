;;;; LambdaCalc examples
;;;; examples.scm
;;;; Copyright 2023 Billy Brown
;;;; This Source Code Form is subject to the terms of the Mozilla Public
;;;; License, v. 2.0. If a copy of the MPL was not distributed with this
;;;; file, You can obtain one at https://mozilla.org/MPL/2.0/.

(load "lambdacalc.scm")

(display "Example 1")
(newline)

(display
  (evaluate
    (lambda-cfg
      (lex "let double = (n . n + n), (double 5);"))))
(newline)
