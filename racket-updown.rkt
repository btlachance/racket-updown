#lang racket
(module updown racket
  (require (for-syntax syntax/parse racket/syntax)
           syntax/location
           rackunit)
  (provide #%top-interaction
           trace-eval
           check-equal?
           check-code?
           (rename-out [ud:module-begin #%module-begin]
                       [ud:lambda lambda]
                       [ud:app #%app]
                       [ud:datum #%datum]
                       [ud:if0 if0]
                       [ud:lift lift]
                       [ud:run run]))

  (struct code (e)
    #:methods gen:custom-write
    [(define (write-proc v port mode)
       (pretty-display
        (format
         "(code ~a)"
         (syntax->datum (code-e v)))
        port
        #:newline? #f))])
  (define not-code? (negate code?))

  (define-syntax (define-prims stx)
    (syntax-parse stx
      [(_ prim-name:id ...)
       (define (make-prim-id id) (format-id id "ud:~a" id))
       (with-syntax ([(ud:prim ...) (map make-prim-id (attribute prim-name))])
         #`(begin
             (define ud:prim (prim prim-name #'ud:prim)) ...
             (provide (rename-out [ud:prim prim-name] ...))))]))
  (struct prim (proc id)
    #:property prop:procedure (struct-field-index proc))
  (define-prims + add1 sub1)

  (define-syntax (ud:lambda stx)
    (syntax-parse stx
      [(_ rec:id (x:id) e:expr)
       (with-syntax ([raw-rec (format-id #'rec "raw-~a" #'rec)])
         ;; A bit of a mess but it lets us use the normal Racket
         ;; calling convention and still replace the self-reference
         ;; with code
         #`(letrec ([raw-rec (lambda (rec x) e)]
                    [rec (liftable-proc
                          (procedure-rename
                           (lambda (x) (raw-rec rec x))
                           'rec)
                          raw-rec #'rec #'x #'e)])
             rec))]))
  (struct liftable-proc (value raw-value rec arg body)
    #:property prop:procedure (struct-field-index value))

  (define-syntax (ud:datum stx)
    (syntax-parse stx
      [(_ . d:number) #`(#%datum . d)]))

  (define-syntax (ud:app stx)
    (syntax-parse stx
      [(_ e ...)
       ;; TODO Ditch call-or-code (and thus apply) by compiling to
       ;; match*/case dispatch/function applications here
       #`(call-or-code (list e ...) #'(e ...))]))
  ;; App needs to either produce a value or produce code. First, we
  ;; run the arguments down to a list of values (which gets bound to
  ;; args). We implicitly lift primitive functions, but I'm not sure
  ;; if that's the right thing to do---what if it was an effectful
  ;; operation that evaluated to a prim?---maybe they should have to
  ;; be explicitly lifted.
  (define (call-or-code args stxs)
    (match* ((car args) (cdr args))
      [((or (prim _ e-rator) (code e-rator))
        (list (code e-rands) ...))
       (code #`(ud:app #,e-rator #,@e-rands))]

      [((or (prim rator _) (? liftable-proc? rator))
        (list rands ...))
       (apply rator rands)]))

  (define-syntax-rule (ud:if0 e1 e2 e3)
    (match e1
      [(code e)
       (match* (e2 e3)
         [((code e2*) (code e3*))
          (code #`(ud:if0 #,e #,e2* #,e3*))])]
      [0 e2]
      [_ e3]))

  (define-syntax-rule (ud:lift e) (lift e))
  (define (lift v)
    (define v-exp
      (match v
        [(? number? v) #`(ud:datum . #,v)]
        [(liftable-proc proc raw-proc rec arg _)
         (define rec-fresh (datum->syntax #'rec (syntax-e rec)))
         (define arg-fresh (datum->syntax #'arg (gensym (syntax-e arg))))

         (match (raw-proc (code rec-fresh) (code arg-fresh))
           [(code e)
            #`(ud:lambda
               #,rec-fresh (#,arg-fresh)
               #,e)])]
         [(prim _ id) id]
         [(code e) #`(ud:lift #,e)]))
    (code v-exp))
  (define print-eval? (make-parameter #f))
  (define-syntax (trace-eval stx)
    (syntax-parse stx
      [(_ e ...+)
       #`(parameterize ([print-eval? #t])
           e ...)]))

  (define (eval-code-exp e)
    (when (print-eval?) (displayln (format "evaluating ~a" (syntax->datum e))))
    (define result (eval e (eval-namespace)))
    (when (print-eval?)
      (match result
        [(? liftable-proc? p)
         (displayln (format "produced proc with body ~a" (syntax->datum (liftable-proc-body p))))]
        [(code body)
         (displayln (format "produced code for ~a" (syntax->datum body)))]
        [_ (displayln (format "produced ~a" result))]))
    result)
  (define-syntax-rule (ud:run b e)
    (match b
      [(code b1)
       (code
        (match e
          [(code e-code) #`(ud:run #,b1 #,e-code)]))]
      [_
       (match e
         [(code e-code) (eval-code-exp e-code)])]))

  (define eval-namespace (make-parameter #f))
  (define-syntax (ud:module-begin stx)
    (syntax-parse stx
      [(_ forms ...+)
       #`(#%module-begin
          ;; Avoid parameterize around the module body because I don't
          ;; know a way for that to work w/printing-module-begin
          (let ([ns (make-base-empty-namespace)])
            ;; Use namespace-attach-module because we need to share
            ;; the eval-namespace parameter (or something like that,
            ;; see https://goo.gl/ihKPSH)
            (namespace-attach-module (current-namespace)
                                     (quote-module-path ".." updown)
                                     ns)
            (parameterize ([current-namespace ns])
              ;; How to properly refer to the updown module? IDK, but
              ;; maybe that will be easier once it has a/is an
              ;; installed collection
              (namespace-require (quote-module-path ".." updown)))
            (eval-namespace ns))
          forms ...)]))
  (define-syntax-rule (check-code? e)
    (check-pred code? e)))

(module test (submod ".." updown)
  ;; Datum can be lifted/run
  (check-code? (lift (add1 1)))
  (check-equal? (run 0 (lift (add1 1))) 2)


  ;; Run produces code when the first arg is code
  (check-code? (run (lift 1) (lift 5)))
  (check-equal? (run 0 (run (lift 1) (lift (lift 11)))) 11)


  ;; if0 does the right thing on non-code and code
  (check-equal? (if0 0 111 999) 111)
  (check-equal? (if0 1 9 400) 400)
  (check-code? (if0 (lift 5) (lift 111) (lift 999)))
  (check-equal? (run 0 (if0 (lift 1) (lift 10) (lift 11))) 11)


  ;; Lambdas and primitive operators do the right thing on non-code
  (check-equal? (((lambda _ (x) (lambda _ (y) x)) 1) 404) 1)
  (check-equal? ((lambda _ (x) (add1 x)) 5) 6)
  (check-equal? (sub1 10) 9)


  ;; Primitive operators produce code when giving code arguments (and
  ;; they can also be lifted)
  (check-equal? (run 0 (+ (lift 1) (lift 2))) 3)
  (check-equal? (run 0 ((lift +) (lift 1) (lift 2))) 3)


  (check-equal? ((lambda sum (n) (if0 n n (+ n (sum (sub1 n))))) 5)
                15)
  ;; Lambdas do the right thing when lifted/run
  (check-equal? ((run 0 (lift (lambda _ (x) (x (lift 41))))) add1)
                42)
  (check-equal? ((run 0 (lift (lambda sum (n) (if0 n n (+ n (sum (sub1 n))))))) 6)
                21)


  ;; Make sure that lambdas inside a lifted function can close over
  ;; arguments to the lifted function.
  (check-equal?
   (((run 0 (lift (lambda _ (x) (if0 x x (lift (lambda _ (y) x)))))) 42) 0)
   42))
