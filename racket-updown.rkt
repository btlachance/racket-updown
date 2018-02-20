#lang racket
(module updown racket
  (require (for-syntax syntax/parse)
           syntax/location
           rackunit)
  (provide #%top-interaction
           check-equal?
           check-pred
           negate
           number?
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
    (pretty-display (syntax->datum exp) port #:newline? #f)
    (pretty-display ">" port #:newline? #f))
  (struct code (e)
    #:transparent
    #:methods gen:custom-write
    [(define write-proc code-print)])

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

  (define-syntax (ud:app stx)
    (syntax-parse stx
      [(_ e-op e-arg)
       #`(match* (e-op e-arg)
           [((code op) (code arg)) (code #`(ud:app (void) (void)))]
           [((? liftable-proc? v-op) v-arg) (#%app v-op v-op v-arg)]
           [(v1 v2) (#%app v1 v2)])]
      [(_ e ...)
       #`(#%app e ...)]))

  (define-syntax (ud:if0 stx)
    (syntax-parse stx
      [(_ e1 e2 e3)
       #`(match e1
           [(code e) (code #`(ud:if0 #,e (void) (void)))]
           [(? zero? _) e2]
           [_ e3])]))

  (define (lift v)
    (define v-exp
      (match v
        [(? number? v) #`(ud:datum . #,v)]
        [(liftable-proc proc rec arg body)
         #`(ud:lambda
            #,rec (#,arg)
            (void))]
        [(code e) #`(ud:lift #,e)]))
    (code v-exp))
  (define-syntax (ud:lift stx)
    (syntax-parse stx
      [(_ e) #`(lift e)]))

  (define (eval-code-exp e) (eval e (eval-namespace)))
  (define-syntax (ud:run stx)
    (syntax-parse stx
      [(_ b e)
       #`(match b
           [(code b1)
            (code
             (match e
               [(code e-code) #`(ud:run #,b1 #,e-code)]))]
           [_
            (match e
              [(code e-code) (eval-code-exp e-code)])])]))

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
          forms ...)])))

(module test (submod ".." updown)
  (check-equal? 5 (run 0 (lift 5)))
  (check-pred (negate number?) (run (lift 1) (lift 5)))
  (check-equal? 11 (run 0 (run (lift 1) (lift (lift 11)))))

  (check-equal? 111 (if0 0 111 999))
  (check-pred (negate number?) (if0 (lift 5) 111 999)))

(module main (submod ".." updown)
  (run 0 (lift 6))
  (if0 ((lambda _ (x) x) 1)
       111
       999)
  (if0 (lift 5) 111 999))
