#lang racket
(module updown racket
  (require (for-syntax syntax/parse)
           syntax/location
           rackunit)
  (provide #%top-interaction
           check-equal?
           check-code?
           negate
           number?
           add1
           sub1
           (rename-out [ud:module-begin #%module-begin]
                       [ud:lambda lambda]
                       [ud:app #%app]
                       [ud:datum #%datum]
                       [ud:if0 if0]
                       [ud:lift lift]
                       [ud:run run]))

  (define (code-print c port mode)
    (define exp (code-e c))
    (pretty-display "<code " port #:newline? #f)
    (pretty-display
     ;; Haven't thought through why arbitrary values ended up in code
     ;; in the first place
     (if (syntax? exp)
         (syntax->datum exp)
         exp)
     port #:newline? #f)
    (pretty-display ">" port #:newline? #f))
  (struct code (e)
    #:transparent
    #:methods gen:custom-write
    [(define write-proc code-print)])
  (define not-code? (negate code?))

  (struct liftable-proc (value rec arg body)
    #:property prop:procedure (struct-field-index value))


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
      [(_ . datum) #`(#%datum . datum)]))

  ;; Only values of certain expressions can participate in an implicit
  ;; lifting. This restriction is mostly because of side effects: if
  ;; an expression could have side effects, I'm not confident I want
  ;; to produce a code version of that expression after I already
  ;; evaluated the expresson once. The `simple?` below is given the
  ;; expression a user wrote, which probably isn't safe if I want the
  ;; side-effect eliminating part of things to be sound (e.g. what if
  ;; stx is an identifer that expands to something complex?). But it's
  ;; a start. Maybe this is another reason why let-insertion is useful
  ;; (but if the core of my language was ANF'd before any runtime,
  ;; then maybe implicit lifting would be just as easy...)
  (define (simple? stx)
    (or (identifier? stx)
        (number? (syntax-e stx))))
  (define (bad-implicit-lift datum)
    (error "implicit lift of non-simple:" datum))

  (define-syntax (ud:app stx)
    (syntax-parse stx
      [(_ e-op e-arg)
       #`(match* (e-op e-arg)
           [((? not-code? op) (code arg))
            (unless (simple? #'e-op)
              (bad-implicit-lift (syntax->datum #'e-op)))
            (code #`(ud:app e-op #,arg))]
           [((code op) (? not-code? arg))
            (unless (simple? #'e-arg)
              (bad-implicit-lift (syntax->datum #'e-arg)))
            (code #`(ud:app #,op e-arg))]
           [((code op) (code arg)) (code #`(ud:app #,op #,arg))]
           [(v1 v2)
            (if (liftable-proc? v1)
                (#%app v1 v1 v2)
                (#%app v1 v2))])]
      [(_ e ...)
       #`(#%app e ...)]))

  (define-syntax-rule (ud:if0 e1 e2 e3)
    (match e1
      [(code e) (code #`(ud:if0 #,e (void) (void)))]
      [(? zero? _) e2]
      [_ e3]))

  (define (fresh-var [name 'var]) (gensym name))
  (define (lift v [mumble #f])
    (define v-exp
      (match v
        [(? number? v) #`(ud:datum . #,v)]
        [(liftable-proc proc rec arg body)
         (define rec-fresh (fresh-var (syntax-e rec)))
         (define arg-fresh (fresh-var (syntax-e arg)))
         #`(ud:lambda
            #,rec-fresh (#,arg-fresh)
            #,(match (eval-code-exp #`((ud:lambda #,rec (#,arg) #,body)
                                       #,(code rec-fresh) #,(code arg-fresh)))
                [(code reduced-body) reduced-body]
                [(? not-code? v) v]))]
        ;; What should happen if we lift an arbitrary function? Maybe
        ;; we have to only allow lifting liftable-proc and primitive
        ;; functions (e.g. add1)
        ;; [(? procedure? p) ...]
        [(code e) #`(ud:lift #,e)]))
    (code v-exp))
  (define-syntax-rule (ud:lift e) (lift e))

  (define (eval-code-exp e) (eval e (eval-namespace)))
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
          ;; Avoid parameterize because I don't know a different way
          ;; to work with printing-module-begin
          (let ([ns (make-base-empty-namespace)])
            ;; Need the eval-namespace parameter to be shared (or
            ;; something like that, see https://goo.gl/ihKPSH)
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

  (check-equal? (((lambda _ (x) (lambda _ (y) x)) 1) 404) 1)

  (check-equal? ((lambda _ (x) (add1 x)) 5) 6)
  (check-equal? (sub1 10) 9)

  (check-code? (lift (lambda _ (x) (add1 11))))
  (check-equal? ((run 0 (lift (lambda _ (x) (add1 11)))) 42)
                12)
  (check-code? (lift (lambda _ (x) (x 1))))
  (check-equal? ((run 0 (lift (lambda _ (x) (x 41)))) (lambda _ (x) x)) 41)
  (check-equal? ((run 0 (lift (lambda _ (x) (add1 x)))) 42)
                43))
