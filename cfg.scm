;;;; Context-Free Grammar (CFG)
;;;; cfg.scm
;;;; Copyright 2019 Billy Brown

;;;; Macro to generate a CFG from a BNF Scheme macro.
;;;; The generated CFG is a function that takes a list of lists,
;;;; in which the first element of every list is a pair where the
;;;; car is the token and the cdr is the data attached to the token.
;;;; For examples, see the EXAMPLES section.

(use srfi-1)

(define-syntax cfg
  (syntax-rules (:=)
    ((cfg
       (production := first-token token ...)
       ...)
     (lambda (tokens)
       ; Generate the POST sets for the productions, in order to determine
       ; when a reduction can be made
       (let* ((productions (list (list (quote production)
                                       (quote first-token)
                                       (quote token)
                                       ...)
                                 ...))
              (posts (post-sets productions)))
         (if (null? tokens)
             #t
             (let loop ((stack '())
                        (input tokens))
               (cond
                 ; Can the stack be reduced using this production
                 ((and (can-reduce? (reverse (list (quote first-token)
                                                   (quote token)
                                                   ...))
                                    stack)
                       ; Is the next input symbol (if there is one) in
                       ; this production's non-terminal's POST set?
                       (let ((post (assv (quote production) posts)))
                         (if (and post (not (null? input)))
                             (memv (caar input) post)
                             #t)))
                  ; Take the elements off the stack
                  (let* ((num-pop (length (list (quote first-token) (quote token) ...)))
                         (popped (reverse (take stack num-pop)))
                         (stack (drop stack num-pop)))
                    ; Reduce the popped elements into this production's non-terminal
                    (loop (cons
                            (cons (quote production)
                                  popped)
                            stack)
                          input)))
                 ...
                 ; Return the stack when the input runs out
                 ((null? input)
                  stack)
                 ; Otherwise shift a token from the input onto the stack
                 (else
                   (loop (cons (car input)
                               stack)
                         (cdr input)))))))))))

;;;; EXAMPLES ;;;;

(define example-cfg-1
  (cfg (S := E semi-colon E)
       (S := E semi-colon)
       (E := E + E)
       (E := V * V)
       (E := V)
       (V := int)))

(define example-tokens-1
  '((int . 4) (+) (int . 2) (semi-colon) (eof)))
(define example-tokens-1-parsed
  '((S
      (E
        (E
          (V
            (int . 4)))
        (+)
        (E
          (V
            (int . 2))))
      (semi-colon))))

(define example-cfg-2
  (cfg
    (S := var label = E)
    (E := E + E)
    (E := label)
    (E := int)))

(define example-tokens-2
  '((var) (label . "x") (=) (int . 4) (+) (int . 2)))
(define example-tokens-2-parsed
  '((S
      (var)
      (label . "x")
      (=)
      (E
        (E
          (int . 4))
        (+)
        (E (int . 2))))))

;;;; IMPLEMENTATION ;;;;

(define (can-reduce? symbols stack)
  (cond
    ((and (not (null? symbols))
          (null? stack))
     #f)
    ((null? symbols)
     #t)
    ((eqv? (car symbols) (caar stack))
     (can-reduce? (cdr symbols) (cdr stack)))
    (else
      #f)))

;;; Find the PRE sets: all terminals that may appear at the beginning
;;; of an expanded non-terminal production.
;;; Find the POST sets: all terminals that may appear directly after
;;; an expanded non-terminal production. These are the terminals and
;;; PRE set elements of the non-terminals that follow occurrences of
;;; a non-terminal in the rhs of productions, or the POST set of the
;;; production's own lhs non-terminal if this one occurs last.
;;;
;;; To find the PRE sets:
;;;   PRE = [ (lhs, { first symbol of rhs }) for lhs:rhs in productions ]
;;;   Repeat until PRE contains no more non-terminals:
;;;     Take a non-terminal from the PRE set
;;;     If it is not this PRE set's non-terminal:
;;;       Replace it with that non-terminal's own PRE set
;;;
;;; To find the POST sets:
;;;   non-terminals = { lhs for lhs:_ in productions }
;;;   POST_1 = [ (non-terminal, { y for (x, y) in symbol-pairs(rhs)
;;;                               for _ in productions
;;;                               where x = non-terminal
;;;                             })
;;;              for non-terminal in non-terminals
;;;            ]
;;;   Repeat until POST_1 contains no more non-terminals:
;;;     Take a non-terminal from the POST_1 set
;;;     Replace it with that non-terminal's PRE set
;;;   POST_2 = [ (non-terminal, { lhs
;;;                               for lhs:rhs in productions
;;;                               where last(rhs) = non-terminal
;;;                             })
;;;              for non-terminal in non-terminals
;;;            ]
;;;   POST = Merge POST_1 and POST_2
;;;   Repeat until POST contains no more non-terminals:
;;;     Take a non-terminal from the POST set
;;;     Replace it with that non-terminal's POST set

;;; PRE ;;;

(define (pre-sets productions)
  (let ((non-terminals (uniqv (map car productions)))
        (pres (pre-sets/initial productions)))
    ; If any non-terminals remain in the PRE sets, expand again
    (repeated-application
      (lambda (expanded)
        (any (lambda (pre)
               (not (null? (set-intersection (cdr pre)
                                             non-terminals))))
             expanded))
      pre-sets/expand
      pres)))

(define (pre-sets/initial productions)
  (let ((first-symbols (assv/union (map (lambda (production)
                                          (list (car production)
                                                (cadr production)))
                                        productions))))
    (map uniqv first-symbols)))

(define (pre-sets/expand pres)
  (map (lambda (pre)
         (let ((lhs (car pre))
               (rhs (cdr pre)))
           (uniqv
             (cons lhs
                   (fold (lambda (symbol pre)
                           (let ((parent (assv symbol pres)))
                             (if parent
                                 (set-union pre (cdr parent))
                                 (cons symbol pre))))
                         '()
                         rhs)))))
       pres))

;;; POST ;;;

(define (post-sets productions)
  (let* ((non-terminals (uniqv (map car productions)))
         (pres (pre-sets productions))
         (posts/following (post-sets/initial/following productions non-terminals)))
    (let* ((posts/following (repeated-application (lambda (posts)
                                                    (post/non-terminals? posts non-terminals))
                                                  (lambda (posts)
                                                    (post-sets/expand/pre posts pres))
                                                  posts/following))
           (posts/parent (post-sets/initial/parent productions non-terminals))
           (posts (assv/union posts/following posts/parent)))
      (repeated-application (lambda (posts)
                              (post/non-terminals? posts non-terminals))
                            post-sets/expand/post
                            posts))))

(define (post-sets/initial/following productions non-terminals)
  ; If the non-terminal appears in the rhs, add the following symbol
  (assv/union (map (lambda (non-terminal)
                     (cons
                       non-terminal
                       (fold (lambda (production post)
                               (append
                                 post
                                 (post/following-symbols
                                   non-terminal
                                   (cdr production))))
                             '()
                             productions)))
                   non-terminals)))

(define (post-sets/initial/parent productions non-terminals)
  ; If the non-terminal appears last in the rhs, add the lhs
  (assv/union (map (lambda (non-terminal)
                     (let ((posts (fold (lambda (production post)
                                          (append
                                            post
                                            (post/parent-when-last
                                              non-terminal
                                              production)))
                                        '()
                                        productions)))
                       ; Add the eof terminal to the POST list of the
                       ; first production
                       (cons
                         non-terminal
                         (if (eqv? non-terminal (caar productions))
                             (cons 'eof posts)
                             posts))))
                   non-terminals)))

(define (post-sets/expand/pre posts pres)
  (map (lambda (post)
         (let ((lhs (car post))
               (rhs (cdr post)))
           (uniqv
             (cons lhs
                   (fold (lambda (symbol post)
                           ; Try finding a PRE set for this symbol
                           (let ((non-terminal (assv symbol pres)))
                             (if non-terminal
                                 ; If there is one, union the non-terminal's
                                 ; PRE set with this non-terminal's POST set
                                 (set-union post (cdr non-terminal))
                                 (cons symbol post))))
                         '()
                         rhs)))))
       posts))

(define (post-sets/expand/post posts)
  (map (lambda (post)
         (let ((lhs (car post))
               (rhs (cdr post)))
           (uniqv
             (cons lhs
                   (fold (lambda (symbol post)
                           ; Try finding a POST set for this symbol
                           (let ((non-terminal (assv symbol posts)))
                             (if non-terminal
                                 ; If there is one, union the non-terminal's
                                 ; POST set with this non-terminal's POST set
                                 (set-union post (cdr non-terminal))
                                 (cons symbol post))))
                         '()
                         rhs)))))
       posts))

(define (post/following-symbols non-terminal rhs)
  (cond
    ((or (null? rhs) (null? (cdr rhs)))
     '())
    ((eqv? non-terminal (car rhs))
     (cons (cadr rhs)
           (post/following-symbols non-terminal (cdr rhs))))
    (else
      (post/following-symbols non-terminal (cdr rhs)))))

(define (post/parent-when-last non-terminal production)
  (let ((parent (car production))
        (last (car (reverse production))))
    (if (eqv? non-terminal last)
        (list parent)
        '())))

(define (post/non-terminals? posts non-terminals)
  (any (lambda (post)
         (not (null? (set-intersection (cdr post) non-terminals))))
       posts))

;;; HELPERS ;;;

(define (repeated-application pred? func param)
  (if (pred? param)
      (repeated-application
        pred?
        func
        (func param))
      param))

(define (assv/del object alist)
  (cond
    ((null? alist)
     '())
    ((eqv? object (caar alist))
     (assv/del object (cdr alist)))
    (else
      (cons (car alist)
            (assv/del object (cdr alist))))))

(define (assv/union . alists)
  (fold (lambda (elem alist)
          (let ((found (assv (car elem) alist)))
            (if found
                (cons 
                  (cons (car elem)
                        (set-union (cdr found)
                                   (cdr elem)))
                  (assv/del (car elem) alist))
                (cons elem alist))))
        '()
        (apply append alists)))

(define (uniqv lat)
  (reverse
    (fold (lambda (x rest)
            (if (memv x rest)
                rest
                (cons x rest)))
          '()
          lat)))

(define (unique lat)
  (reverse
    (fold (lambda (x rest)
            (if (member x rest)
                rest
                (cons x rest)))
          '()
          lat)))

(define (set-union s1 s2 . sets)
  (letrec ((bi-union (lambda (s1 s2 s)
                       (cond
                         ((and (null? s1)
                               (null? s2))
                          s)
                         ((null? s1)
                          (bi-union s2 s1 s))
                         (else
                           (let ((element (car s1)))
                             (if (memv element s)
                                 (bi-union (cdr s1) s2 s)
                                 (bi-union (cdr s1) s2 (cons element s)))))))))
    (let ((s (bi-union s1 s2 '())))
      (if (null? sets)
          s
          (apply set-union (cons s sets))))))

(define (set-intersection s1 s2 . sets)
  (letrec ((bi-intersection (lambda (s1 s2)
                              (cond
                                ((or (null? s1)
                                     (null? s2))
                                 '())
                                ((memv (car s2) s1)
                                 (cons (car s2)
                                       (bi-intersection s1 (cdr s2))))
                                (else
                                  (bi-intersection s1 (cdr s2)))))))
    (let ((s (bi-intersection s1 s2)))
      (if (null? sets)
          (uniqv s)
          (apply set-intersection (cons s sets))))))
