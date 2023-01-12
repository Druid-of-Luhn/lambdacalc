;;;; Pattern Matching for Scheme
;;;; Copyright 2020, 2022 Billy Brown
;;;;
;;;; Table of Contents
;;;; =================
;;;; - Implementation
;;;;   - pattern-match : macro
;;;;   - pattern-match/bind : 'a -> 'b -> [(symbol 'c)]
;;;;   - pattern-match/quoted-symbol? : 'a -> bool
;;;;   - pattern-match/quoted-symbol->symbol : (symbol symbol) -> symbol
;;;;   - pattern-match/@-symbol? : 'a -> bool
;;;;   - pattern-match/@-symbol->symbol : 'a -> Either bool symbol
;;;;   - pattern-match/unify : [(symbol 'a)] -> [(symbol 'a)] -> Either bool [(symbol 'a)]
;;;; - Examples
;;;;   - pattern-match/example-1 : ()
;;;;   - pattern-match/example-2 : ()
;;;;   - pattern-match/example-3 : 'a -> 'b -> ()
;;;;   - pattern-match/example-4 : ()
;;;;   - pattern-match/example-5 : ()

;;; Implementation

;; Pattern match on a value and execute the expressions of the first match.
;; This macro uses the `pattern-match/bind` function to determine whether a
;; value matches a given pattern and to perform any bindings defined in the
;; pattern. The desired name of a getter method is passed to the macro, and
;; a function is made available to the expressions executed in the matching
;; branch that bears that name and takes a symbol, and returns the value 
;; associated with that symbol in the pattern match's bindings.
(define-syntax pattern-match
  (syntax-rules (else)
    ((pattern-match value getter-name
                    (pattern body ...)
                    ...
                    (else otherwise ...))
     (cond
       ((pattern-match/bind value (quote pattern))
        => (lambda (bindings)
             (let ((getter-name (lambda (id)
                                  (let ((found (assv id bindings)))
                                    (if found
                                        (cadr found)
                                        #f)))))
               body
               ...)))
       ...
       (else
         otherwise
         ...)))))

;; Create a list of bindings from a pattern and a value to match it to.
;; If the value could not be made to match the pattern, then false `#f` is
;; returned. If a pattern match can be made, then a list of lists is returned,
;; where the car of the sub-list is a symbol and the cdr is the value bound to
;; that symbol.
;; Patterns need not bind values to symbols in order to pass, in which case an
;; empty list of bindings is returned.
;; The pattern argument must double-quote `(quote (quote symbol))` symbols if
;; that symbol must match a symbol in the argument to match. If a symbol is
;; quoted only once, then it is considered to be an identifier, to which a
;; sub-structure of the value may be bound
(define (pattern-match/bind value pattern)
  (cond
    ; If the pattern is a pair with its first item being a single quoted symbol
    ; beginning with the @ character, it's a binding on the whole value, while
    ; the value is still to be pattern-matched further by the second item of
    ; the pair.
    ((and (pair? pattern)
          (not (null? pattern))
          (not (null? (cdr pattern)))
          (pattern-match/@-symbol? (car pattern)))
     (pattern-match/unify (list (list (pattern-match/@-symbol->symbol (car pattern)) value))
                          (pattern-match/bind value (cadr pattern))))
    ; If the pattern is a single-quoted symbol, it's a binding!
    ((and (symbol? pattern)
          (not (pattern-match/quoted-symbol? pattern)))
     (list (list pattern value)))
    ; If they're both empty, it's a match!
    ((and (null? value)
          (null? pattern))
     '())
    ; If one but not the other is empty, it's not a match... :(
    ((or (null? value)
         (null? pattern))
     #f)
    ; If they're both the same quoted symbols, it's a match!
    ; This is a special case, because symbols in the pattern must be
    ; double-quoted, otherwise they are identifiers (handled above).
    ((and (symbol? value)
          (pattern-match/quoted-symbol? pattern)
          (eqv? value (pattern-match/quoted-symbol->symbol pattern)))
     '())
    ; If they're both the same atoms, it's a match!
    ((and (atom? value)
          (atom? pattern)
          (equal? value pattern))
     '())
    ; If they're both pairs, then try recursively matching them...
    ((and (pair? value) (pair? pattern))
     (let ((lhs (pattern-match/bind (car value) (car pattern)))
           (rhs (pattern-match/bind (cdr value) (cdr pattern))))
       (pattern-match/unify lhs rhs)))
    ; We've run out of options; it's not a match... :(
    (else #f)))

;; Is the given value a quoted symbol?
;; A quoted symbol has the form `(quote symbol)`, which is a list of two
;; symbols: the car is `quote` and the cdr is the symbol that is quoted.
(define (pattern-match/quoted-symbol? value)
  (and (list? value)
       (not (null? value))
       (not (null? (cdr value)))
       (null? (cddr value))
       (eqv? (car value) 'quote)
       (symbol? (cadr value))))

;; Extract the symbol from a quoted symbol.
;; This function expects a value that is accepted by the
;; `pattern-match/quoted-symbol?` predicate and returns the symbol.
(define pattern-match/quoted-symbol->symbol cadr)

;; Is the given value an unquoted symbol beginning with an @?
(define (pattern-match/@-symbol? value)
  (and (symbol? value)
       (not (pattern-match/quoted-symbol? value))
       (char=? #\@ (car (string->list (symbol->string value))))))

;; Get the name of the @ symbol without the @.
(define (pattern-match/@-symbol->symbol value)
  (if (pattern-match/@-symbol? value)
    (string->symbol (list->string (cdr (string->list (symbol->string value)))))
    #f))

;; Unify two branches of a pattern-match bind.
;; Unification is performed as a set union of the two bindings, with one
;; special case: if each branch contains an assignment for an identifier, then
;; that assignment must be the same in both branches. If it is not, then the
;; whole pattern-match fails.
;; Complexity: O(n * m) where n = (length lhs) and m = (length rhs).
(define (pattern-match/unify lhs rhs)
  (cond
    ;; Recursive base case: if either branch failed, propagate the failure
    ((or (not lhs) (not rhs))
     #f)
    ;; Recursive base case: if the right-hand-side bindings are empty, then
    ;; return the left-hand-side bindings
    ((null? rhs)
     lhs)
    ;; Recursive base case: if the left-hand-side bindings are empty, then
    ;; return the right-hand-side bindings
    ((null? lhs)
     rhs)
    ;; Recursive step: look for the first right-hand-side binding in the
    ;; list of left-hand-side bindings. If it is present in the left-hand-side
    ;; but the assignments do not match, this pattern-match fails; otherwise
    ;; recurse, holding on to the first right-hand-side binding if it does not
    ;; appear on the left-hand-side, and continuing with the rest of the
    ;; right-hand-side binding.
    (else
      (let ((found (assv (caar rhs) lhs)))
        (cond
          ((and found (equal? found (car rhs)))
           (pattern-match/unify lhs (cdr rhs)))
          (found
            #f)
          (else
            (cons (car rhs)
                  (pattern-match/unify lhs (cdr rhs)))))))))

;;; Examples

(import (chicken format))

;; Example 1: match the first de-structured pattern and bind a sub-part.
(define (pattern-match/example-1)
  (let ((e '(E (NAME (identifier . "x")))))
    (pattern-match e get
                   (('E ('NAME ('identifier . id)))
                    (printf "identifier: ~A~%" (get 'id))
                    (get 'id))
                   (x
                     (printf "expression: ~A~%" (get 'x))
                     (get 'x))
                   (else
                     (printf "failed~%")
                     #f))))

;; Example 2: match the second non-de-structured pattern and bind it all.
(define (pattern-match/example-2)
  (let ((e '(ES (E (NAME (identifier . "x"))))))
    (pattern-match e get
                   (('E ('NAME ('identifier . id)))
                    (printf "identifier: ~A~%" (get 'id))
                    (get 'id))
                   (x
                     (printf "expression: ~A~%" (get 'x))
                     (get 'x))
                   (else
                     (printf "failed~%")
                     #f))))

;; Example 3: pass two values to the function; a pattern match is performed
;; that attempts to assign both values to the same symbol. If the values are
;; equal, then the pattern match will succeed. If not, then it will fail.
;; Success or failure is determined only by a printed message.
(define (pattern-match/example-3 a b)
  (pattern-match (list 'pair a b) get
                 (('pair x x)
                  (printf "pair (~A . ~A)~%" (get 'x) (get 'x)))
                 (else
                   (printf "Items in the pair are not equal.~%"))))

;; Example 4: perform a nested pattern-match with unshadowed getters.
;; This enables the internal pattern-match to access both its own bindings and
;; its parent pattern-match's bindings.
;; If the getter were to be shadowed, then all bindings from the outer pattern-
;; match would be made unavailable, regardless of whether they themselves were
;; shadowed by the inner pattern-match's variables.
(define (pattern-match/example-4)
  (let ((e '(PAIR (NAME (identifier . "x"))
                  (NAME (identifier . "y")))))
    (pattern-match e get
                   (('PAIR ('NAME ('identifier . x)) y)
                    (pattern-match (get 'y) get2
                                   (('NAME ('identifier . y))
                                    (printf "pair (~A . ~A)~%" (get 'x) (get2 'y))
                                    #t)
                                   (else
                                     (printf "failed inner~%")
                                     #f)))
                   (else
                     (printf "failed outer~%")
                     #f))))

;; Example 5: assign an expanded pattern to a single identifier.
;; This enables the node to have its structure checked, and maybe even one of
;; its internal elements to be given an identifier, while also assigning an
;; identifier to the whole node.
;; This is like Haskell's name@(Structure other) syntax.
(define (pattern-match/example-5)
  (let ((e '(PAIR (NAME (identifier . "x"))
                  (NAME (identifier . "y")))))
    (pattern-match e get
                   (('PAIR (@first ('NAME ('identifier . x)))
                           second)
                    (printf "pair has first element ~A with name ~A, and second element ~A~%" (get 'first) (get 'x) (get 'second)))
                   (else
                     (printf "failed outer~%")
                     #f))))

;; Example 6: pattern match on the first two elements of a list.
;; This enables the user to ensure that a list has at least N elements, and to
;; extract elements from the front of a list.
;; This is like Haskell's (x1:x2:xs) syntax.
(define (pattern-match/example-6 xs)
  (pattern-match xs get
                 ((a b . cs)
                  (printf "List has at least two elements: ~A, ~A, with remainder ~A~%" (get 'a) (get 'b) (get 'cs)))
                 (else
                   (printf "failed to destructure list~%"
                    #f))))
