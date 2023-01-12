;;;; Lambda Calculus
;;;; lambdacalc
;;;; Copyright 2019 Billy Brown
;;;;
;;;; Usage: (evaluate (lambda-cfg (lex <string>)))

(use extras)

(load "cfg.scm")
(load "patternmatch.scm")

(define lambda-cfg
  (cfg (P := ES eof)
       (ES := E semi-colon)
       (ES := E comma ES)
       (ES := ASSIGN comma ES)
       (ASSIGN := keyword-let NAME equals E)
       (E := open-paren E close-paren)
       (E := APPLY)
       (E := DEFINITION)
       (E := NAME)
       (E := string)
       (E := number)
       (APPLY := E E)
       (APPLY := E operator E)
       (DEFINITION := open-paren NAMES E close-paren)
       (NAMES := NAME period)
       (NAMES := NAMES NAMES)
       (NAME := identifier)))

(define (display-tree tree depth)
  (cond
    ((null? tree))
    ((not (list? tree))
     (printf "~A~A~%" depth tree))
    (else
      (display-tree (car tree) depth)
      (let loop ((tree (cdr tree)))
        (if (null? tree)
            #t
            (begin
              (display-tree (car tree) (string-append depth "| "))
              (loop (cdr tree))))))))

;;;; LEX ;;;;

(define (lex input)
  (let ((lexed (cond
                 ((port? input)
                  (lex-input (make-input input) '()))
                 ((string? input)
                  (lex-input (make-input (open-input-string input)) '()))
                 (else
                   (printf "[lex] Expected a string or a port.~%")
                   #f))))
    (if lexed
        (strip-whitespace lexed)
        #f)))

(define (make-input port)
  (list '() port))

(define (strip-whitespace tokens)
  (filter (lambda (token)
            (not (eqv? (car token) 'whitespace)))
          tokens))

(define lambda-symbols '((#\( . open-paren)
                         (#\) . close-paren)
                         (#\. . period)
                         (#\, . comma)
                         (#\; . semi-colon)
                         (#\= . equals)))
(define lambda-operators '(#\+ #\- #\* #\/ #\% #\^))
(define lambda-keywords '(("let" . keyword-let)))
(define lambda-allowed-identifier-chars
  '(#\_ #\' #\" #\` #\@ #\: #\$ #\? #\# #\|))

(define-syntax pass-values
  (syntax-rules ()
    ((with-values
       body
       function)
     (call-with-values
       (lambda () body)
       function))))

(define (lex-input input tokens)
  (if tokens
      (let-values (((char input) (peek-char input)))
        (cond
          ; Read error
          ((not char)
           #f)
          ; EOF
          ((eof-object? char)
           (reverse (cons '(eof) tokens)))
          ; Whitespace
          ((char-whitespace? char)
           (pass-values (lex-input/whitespace input tokens) lex-input))
          ; Number
          ((char-numeric? char)
           (pass-values (lex-input/number input tokens) lex-input))
          ; Letter
          ((char-alphabetic? char)
           (pass-values (lex-input/identifier input tokens) lex-input))
          ; String
          ((or (char=? char #\") (char=? char #\'))
           (pass-values (lex-input/string input tokens) lex-input))
          ; Symbol
          ((assv char lambda-symbols)
           (pass-values (lex-input/symbol input tokens) lex-input))
          ; Operator
          ((memv char lambda-operators)
           (pass-values (lex-input/operator input tokens) lex-input))
          ; Otherwise error
          (else
            (printf "[lex-input] Unexpected character: ~A~%" char)
            #f)))
      #f))

(define (lex-input/whitespace input tokens)
  ; Pop the first (already seen) character off the input
  (let-values (((_ input) (pop-char input)))
    ; Peek the next (unseen) character off the input, and actually use it
    (let-values (((char input) (peek-char input)))
      (if (and (char? char) (char-whitespace? char))
          (lex-input/whitespace input tokens)
          (values input (cons '(whitespace) tokens))))))

;;; TODO: implement decimal numbers
(define (lex-input/number input tokens . rest)
  ; Pop the first (already seen) character off the input and keep it
  (let-values (((digit input) (pop-char input)))
    ; Peek the next (unseen) character off the input and continue or fail
    (let-values (((char input) (peek-char input)))
      (cond
        ; Recursive case: lex the rest of the number and cons this digit to it
        ((and (char? char)
              (or (char-numeric? char)
                  ; Only allow a decimal point if it has not already been seen
                  (and (char=? char #\.)
                       (or (null? rest) (not (memq 'decimal rest))))))
         (let-values (((input tokens) (apply lex-input/number
                                             (cons input (cons tokens
                                                               ; Keep track of the decimal point
                                                               (if (char=? char #\.)
                                                                   (cons 'decimal rest)
                                                                   rest))))))
           (if tokens
               (values input (cons (cons 'number (cons-number digit (cdar tokens)))
                                   (cdr tokens)))
               (values input #f))))
        ; Positive base case: return the current digit as a number
        ((or (eof-object? char)
             (char-whitespace? char)
             (assv char lambda-symbols)
             (memv char lambda-operators))
         (values input (cons (cons 'number (string->number (string digit))) tokens)))
        ; Failure: unexpected character following numeric character
        (else
          (printf "[lex-input/number] Unexpected character following digit: ~A~%" char)
          (values input #f))))))

(define (lex-input/identifier input tokens)
  ; Pop the first (already seen) character off the input and keep it
  (let-values (((char input) (pop-char input)))
    ; Peek the next (unseen) character off the input and continue or fail
    (let-values (((next-char input) (peek-char input)))
      (cond
        ; Recursive case: lex the rest of the identifier and cons this character to it
        ; Handle the special case for keywords
        ((and (char? next-char)
              (or (char-alphabetic? next-char)
                  (char-numeric? next-char)
                  (memv next-char lambda-allowed-identifier-chars)))
         (let-values (((input tokens) (lex-input/identifier input tokens)))
           (if tokens
               (let* ((identifier (string-append (string char) (cdar tokens)))
                      (maybe-keyword (assoc identifier lambda-keywords)))
                 (values input (cons (cons (if maybe-keyword
                                               (cdr maybe-keyword)
                                               'identifier)
                                           identifier)
                                     (cdr tokens))))
               (values input #f))))
        ; Positive base case: return the current character as an identifier
        ((or (eof-object? next-char)
             (char-whitespace? next-char)
             (assv next-char lambda-symbols)
             (memv next-char lambda-operators))
         (values input (cons (cons 'identifier (string char)) tokens)))
        ; Failure: unexpected character following alphanumeric character
        (else
          (printf "[lex-input/identifier] Unexpected character: ~A~%" next-char)
          (values input #f))))))

(define (lex-input/string input tokens)
  ; Pop the first (already seen quote character) character off the input
  (let-values (((quote-char input) (pop-char input)))
    (let string-loop ((input input)
                      (chars '()))
      (let-values (((char input) (pop-char input)))
        (cond
          ((eof-object? char)
           (printf "[lex-input/string] Unexpected eof~%")
           (values input #f))
          ; End the string when the matching quote character is seen
          ((char=? char quote-char)
           (values input (cons (cons 'string (list->string (reverse chars)))
                               tokens)))
          ; The quote character (and only the quote character) can be escaped
          ((char=? char #\\)
           (let-values (((next-char input) (pop-char input)))
             (if (char=? next-char quote-char)
                 (string-loop input (cons next-char chars))
                 (begin
                   (printf "[lex-input/string] Unexpected escaped character: ~A~%" next-char)
                   (values input #f)))))
          ; ALL other characters are added to the string
          (else
            (string-loop input (cons char chars))))))))

(define (lex-input/symbol input tokens)
  ; Pop the first (already seen) character off the input
  (let-values (((symbol input) (pop-char input)))
    ; Symbols can be followed by anything, so just return its name
    (values input
            (cons (list (cdr (assv symbol lambda-symbols)))
                  tokens))))

(define (lex-input/operator input tokens)
  ; Pop the first (already seen) character off the input
  (let-values (((symbol input) (pop-char input)))
    ; Operators can be followed by anything, so just return it
    (values input (cons (cons 'operator symbol) tokens))))

;;; TODO keep track of line and column numbers
(define (pop-char input)
  (let ((error-message (validate-input input)))
    (cond
      (error-message
        (printf error-message "pop-char")
        (values #f input))
      ((null? (car input))
       (values (read-char (cadr input)) input))
      (else
        ; When popping from the buffered characters,
        ; make sure to remove the character from the buffer.
        (values (caar input)
                (cons (cdar input)
                      (cdr input)))))))

(define (peek-char input)
  (let ((error-message (validate-input input)))
    (cond
      (error-message
        (printf error-message "peek-char")
        (values #f input))
      ((null? (car input))
       ; When peeking from the port, move the character
       ; onto the buffer for later access
       (let ((char (read-char (cadr input))))
         (values char (cons (cons char (car input))
                            (cdr input)))))
      (else
        (values (caar input) input)))))

;;; TODO keep track of line and column numbers
(define (replace-char input char)
  (let ((error-message (validate-input input)))
    (cond
      ((not (char? char))
       (printf "[replace-char] Expected a character.~%")
       input)
      (error-message
        (printf error-message "replace-char")
        (values #f input))
      (else
        (cons (cons char (car input))
              (cdr input))))))

(define (validate-input input)
  (cond
    ((not (list? input))
     "[~A] Expected a list input.~%")
    ((null? input)
     "[~A] Expected a non-empty input.~%")
    ((or (null? (cdr input)) (not (port? (cadr input))))
     "[~A] Expected port in second position of input.~%")
    (else
      #f)))

(define (cons-number digit number)
  (if (and (< number 1) (> number 0))
      (+ (string->number (string digit))
         number)
      (string->number (string-append
                        (string digit)
                        (number->string number)))))

;;;; EVALUATE ;;;;

(define (evaluate program)
  (let-values (((result _env) (evaluate/with-environment program '())))
    result))

(define (evaluate/with-environment element environment)
  (pattern-match
    element get
    ; P := ES eof
    ((('P es ('eof)))
     (printf "P := ES eof~%")
     (evaluate/with-environment (get 'es) environment))
    ; ES := E semi-colon
    (('ES e ('semi-colon))
     (printf "ES := E semi-colon~%")
     (evaluate/with-environment (get 'e) environment))
    ; ES := E comma ES | ASSIGN comma ES
    (('ES e ('comma) es)
     (printf "ES := E|ASSIGN comma ES~%")
     (let-values (((_ environment) (evaluate/with-environment (get 'e) environment)))
       (evaluate/with-environment (get 'es) environment)))
    ; ASSIGN := keyword-let NAME equals E
    (('ASSIGN ('keyword-let . _) ('NAME ('identifier . name)) ('equals) e)
     (printf "ASSIGN := keyword-let NAME equals E~%")
     (let-values (((result environment) (evaluate/with-environment (get 'e) environment)))
       (values result (cons (cons (get 'name) result) environment))))
    ; E := open-paren E close-paren
    (('E ('open-paren) e ('close-paren))
     (printf "E := open-paren E close-paren~%")
     (evaluate/with-environment (get 'e) environment))
    ; E := NAME
    (('E ('NAME ('identifier . name)))
     (printf "E := NAME~%")
     (let ((found (assoc (get 'name) environment)))
       (values
         (if found
             (cdr found)
             (begin
               (printf "[evaluate/with-environment] Variable not found ~A.~%"
                       (get 'name))
               #f))
         environment)))
    ; E := APPLY | DEFINITION | string | number
    (('E x)
     (printf "E := APPLY | DEFINITION | string | number~%")
     (evaluate/with-environment (get 'x) environment))
    ; APPLY := E E
    (('APPLY e1 e2)
     (printf "APPLY := E E~%")
     (let-values (((lhs _) (evaluate/with-environment (get 'e1) environment)))
       (pattern-match
         lhs snd-get
         (('DEFINITION ('open-paren) names e ('close-paren))
          ; Unwrap the first name in the definition, perform beta-reduction for that
          ; name in the lhs with the argument, and then evaluate the result. This could 
          (let-values (((name names) (evaluate/unwrap-names (snd-get 'names))))
            (let ((eval-step (evaluate/beta-reduction
                               (snd-get 'e)
                               (cons name (get 'e2))
                               '())))
              (values (evaluate/with-environment
                        (if (null? names)
                            eval-step
                            (list 'DEFINITION '(open-paren) names eval-step '(close-paren)))
                        environment)
                      environment))))
         (else
           (printf "[evaluate/with-environment] Unexpected lhs in application: ~A.~%" lhs)
           (values #f environment)))))
    ; APPLY := E operator E
    (('APPLY e1 operator e2)
     (printf "APPLY := E operator E~%")
     (let-values (((result1 _env1) (evaluate/with-environment (get 'e1) environment))
                  ((operator _) (evaluate/with-environment (get 'operator) environment))
                  ((result2 _env2) (evaluate/with-environment (get 'e2) environment)))
       (values (operator result1 result2) environment)))
    ; DEFINITION := open-paren NAMES E close-paren
    (('DEFINITION ('open-paren) names e ('close-paren))
     (printf "DEFINITION := open-paren NAMES E close-paren~%")
     (values element environment))
    ; NAMES := NAME period
    (('NAMES n ('period))
     (printf "NAMES := NAME period~%")
     (let-values (((name _) (evaluate/with-environment (get 'n) environment)))
       (values (list name) environment)))
    ; NAMES := NAMES NAMES
    (('NAMES n1 n2)
     (printf "NAMES := NAMES NAMES~%")
     (let-values (((result1 _env1) (evaluate/with-environment (get 'n1) environment))
                  ((result2 _env2) (evaluate/with-environment (get 'n2) environment)))
       (values (append result1 result2)
               environment)))
    ; NAME := identifier
    (('NAME ('identifier . name))
     (printf "NAME := identifier~%")
     (values (get 'name) environment))
    ; string . s
    (('string . s)
     (printf "string . s~%")
     (values (get 's) environment))
    ; number . n
    (('number . n)
     (printf "number . n~%")
     (values (get 'n) environment))
    ; operator . + | - | * | / | % | ^
    (('operator . #\+) (values +      environment))
    (('operator . #\-) (values -      environment))
    (('operator . #\*) (values *      environment))
    (('operator . #\/) (values /      environment))
    (('operator . #\%) (values modulo environment))
    (('operator . #\^) (values expt   environment))
    ; Otherwise
    (else
      (printf "[evaluate/with-environment] Unexpected element ~A.~%" element)
      (values #f environment))))

(define (evaluate/unwrap-names names)
  (pattern-match
    names get
    (('NAMES ('NAME ('identifier . name)) ('period))
     (values (get 'name) '()))
    (('NAMES ('NAMES ('NAME ('identifier . name)) ('period)) ns)
     (values (get 'name) (get 'ns)))
    (('NAMES ns1 ns2)
     (let-values (((name names) (evaluate/unwrap-names (get 'ns1))))
       (values name (list 'NAMES names (get 'ns2)))))
    (else
      (printf "[evaluate/unwrap-names] Unexpected element ~A.~%" names)
      (values #f names))))

(define (evaluate/beta-reduction e arg non-free)
  (pattern-match
    e get
    ; E := open-paren E open-paren <= recurse
    (('E ('open-paren) e ('close-paren))
     (list 'E
           '(open-paren)
           (evaluate/beta-reduction (get 'e) arg non-free)
           '(close-paren)))
    ; E := NAME <= apply the beta-reduction
    (('E ('NAME ('identifier . n)))
     (cond
       ((member (get 'n) non-free)
        ; If the identifier is shadowed, do not beta-reduce it
        (list 'E (list 'NAME (cons 'identifier (get 'n)))))
       ((string=? (get 'n) (car arg))
        (cdr arg))
       (else
         (list 'E (list 'NAME (cons 'identifier (get 'n)))))))
    ; E := APPLY | DEFINITION <= recurse
    (('E x)
     (list 'E (evaluate/beta-reduction (get 'x) arg non-free)))
    ; APPLY := E E <= recurse
    (('APPLY e1 e2)
     (list 'APPLY
           (evaluate/beta-reduction (get 'e1) arg non-free)
           (evaluate/beta-reduction (get 'e2) arg non-free)))
    ; APPLY := E operator E <= recurse
    (('APPLY e1 op e2)
     (list 'APPLY
           (evaluate/beta-reduction (get 'e1) arg non-free)
           (get 'op)
           (evaluate/beta-reduction (get 'e2) arg non-free)))
    ; DEFINITION := open-paren NAMES E close-paren <= keep track of non-free
    (('DEFINITION ('open-paren) names e ('close-paren))
     ((let-values (((names _) (evaluate/with-environment (get 'names) '())))
        (list 'DEFINITION
              '(open-paren)
              (get 'names)
              (evaluate/beta-reduction (get 'e) arg (append names non-free))
              '(close-paren)))))
    ; NAMES := NAME period | NAMES NAMES <= return as-is
    (('NAMES x)
     (list 'NAMES (get 'x)))
    ; NAME := identifier <= return as-is
    (('NAME x)
     (list 'NAME (get 'x)))
    ; string <= return as-is
    (('string . s)
     (cons 'string (get 's)))
    ; number <= return as-is
    (('number . n)
     (cons 'number (get 'n)))
    ; Otherwise
    (else
      (printf "[evaluate/beta-reduction] Unexpected construct: ~A.~%" e)
      #f)))
