#lang racket
(module updown-util racket
  (provide (struct-out code) not-code?)
  (struct code (e) #:prefab)
  (define not-code? (negate code?)))

(module updown racket
  (require (for-syntax syntax/parse (submod ".." updown-util))
           (submod ".." updown-util)
           syntax/location
           rackunit)
  (provide #%top-interaction
           check-equal?
           check-code?
           +
           add1
           sub1
           trace-eval
           (rename-out [ud:module-begin #%module-begin]
                       [ud:lambda lambda]
                       [ud:app #%app]
                       [ud:datum #%datum]
                       [ud:if0 if0]
                       [ud:lift lift]
                       [ud:run run]))


  (define (liftable-proc-print lp port mode)
    (match-define (liftable-proc _ rec arg body) lp)
    (define result
      (format
       "<zliftable-proc ~a (~a) ~a>"
       (syntax-e rec)
       (syntax-e arg)
       (syntax->datum body)))
    (pretty-display result port #:newline? #f))
  (struct liftable-proc (value rec arg body)
    #:property prop:procedure (struct-field-index value)
    #:methods gen:custom-write
    [(define write-proc liftable-proc-print)])


  (define-syntax (ud:lambda stx)
    (syntax-parse stx
      [(_ rec:id (x:id) e:expr)
       #`(liftable-proc
          (lambda (rec x) e)
          #'rec
          #'x
          #'e)]))

  (define-syntax (ud:datum stx)
    (syntax-parse stx
      [(_ . d:number) #`(#%datum . d)]))

  ;; An needs to either produce a value or produce code. First, we run
  ;; the arguments down to a list of values (which get passed as ops).
  ;; But if those values are a mix of code/not code, then we do
  ;; something like an implicit lift (the else case) for the non-code
  ;; ones. That seems sketchy when side-effects get into the mix..
  (define (call-or-code ops stxs)
    (cond
      [(andmap not-code? ops)
       (match-define (cons rator rands) ops)
       (if (liftable-proc? rator)
           (apply rator rator rands)
           (apply rator rands))]
      [else
       (define code-bodies
         (for/list ([v ops]
                    [stx (in-syntax stxs)])
           (if (code? v)
               (code-e v)
               stx)))
       (code #`(ud:app #,@code-bodies))]))

  (define-syntax (ud:app stx)
    (syntax-parse stx
      [(_ e ...)
       #`(call-or-code (list e ...) #'(e ...))]))

  (define-syntax-rule (ud:if0 e1 e2 e3)
    (match e1
      [(code e)
       (match* (e2 e3)
         [((code e2*) (code e3*))
          (code #`(ud:if0 #,e #,e2* #,e3*))]
         [((? not-code? v) (code e3*))
          (match (lift v)
            [(code e2*)
             (code #`(ud:if0 #,e #,e2* #,e3*))])]
         [((code e2*) (? not-code? v))
          (match (lift v)
            [(code e3*)
             (code #`(ud:if0 #,e #,e2* #,e3*))])]
         [((? not-code? v2) (? not-code? v3))
          (match* ((lift v2) (lift v3))
            [((code e2*) (code e3*))
             (code #`(ud:if0 #,e #,e2* #,e3*))])])]
      [(? zero? _) e2]
      [_ e3]))

  (define (fresh-var [name 'var]) (gensym name))
  (define (lift v)
    (define v-exp
      (match v
        [(? number? v) #`(ud:datum . #,v)]
        [(liftable-proc proc rec arg body)
         (define rec-fresh (fresh-var (syntax-e rec)))
         (define arg-fresh (fresh-var (syntax-e arg)))

         #`(ud:lambda
            #,rec-fresh (#,arg-fresh)
            #,(match (eval-code-exp #`((lambda (#,rec #,arg) #,body)
                                       #,(code #`#,rec-fresh) #,(code #`#,arg-fresh)))
                [(code reduced-body)
                 (datum->syntax body reduced-body)]
                [_
                 (error
                  'lift
                  (string-append
                   "Lifting a function evaluates its body, and that body "
                   "must evaluate to code. Instead of code it was: ~a")
                  v)]))]
        ;; What should happen if we lift an arbitrary function? Maybe
        ;; we have to special-case some functions, e.g. wrap add1
        ;; in a liftable-proc
        ;; [(? procedure? p) ...]
        [(code e) #`(ud:lift #,e)]))
    (code v-exp))
  (define-syntax-rule (ud:lift e) (lift e))

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
        [(liftable-proc proc rec arg body)
         (displayln (format "produced proc with body ~a" body))]
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
  (check-code? (lift (add1 1)))
  (check-equal? (run 0 (lift (add1 1))) 2)

  (check-equal? (run 0 (lift 5)) 5)
  (check-code? (run (lift 1) (lift 5)))
  (check-equal? (run 0 (run (lift 1) (lift (lift 11)))) 11)

  (check-equal? (if0 0 111 999) 111)
  (check-equal? (if0 1 9 400) 400)
  (check-code? (if0 (lift 5) 111 999))
  (check-code? (+ (lift 1) 2))

  (check-equal? (((lambda _ (x) (lambda _ (y) x)) 1) 404) 1)

  (check-equal? ((lambda _ (x) (add1 x)) 5) 6)
  (check-equal? (sub1 10) 9)

  (check-equal? ((run 0 (lift (lambda _ (x) (x 41)))) add1)
                42)

  (check-equal? ((lambda sum (n) (if0 n n (+ n (sum (sub1 n))))) 5)
                15)
  (check-code? (lift (lambda sum (n) (if0 n n (+ n (sum (sub1 n)))))))
  (check-equal? ((run 0 (lift (lambda sum (n) (if0 n n (+ n (sum (sub1 n))))))) 6)
                21)

  (check-equal? (run 0 (+ (lift 1) (lift 2))) 3)
  (check-equal? (run 0 (if0 (lift 1) 10 11)) 11))
