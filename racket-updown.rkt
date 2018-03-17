#lang racket
(module updown racket
  (require (for-syntax syntax/parse racket/syntax racket/match racket/pretty)
           syntax/parse
           racket/syntax
           racket/struct
           rackunit)
  (provide #%top-interaction
           trace-eval
           check-equal?
           check-true
           check-code?
           quote
           module+
           (rename-out [ud:module-begin #%module-begin]
                       [ud:lambda lambda]
                       [ud:app #%app]
                       [ud:datum #%datum]
                       [ud:if0 if0]
                       [ud:if if]
                       [ud:lift lift]
                       [ud:run run]
                       [ud:define define]
                       #;(Make sure to update replace-names/exp, too)))

  (struct code (e)
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (lambda (c) 'code)
        (lambda (c) (list (replace-names/exp (code-e c))))))])
  (define not-code? (negate code?))

  (define-syntax (define-prims stx)
    (syntax-parse stx
      [(_ #:id?/name id? #:id->user-sym/name id->user-sym prim-name:id ...)
       (define (make-prim-id id) (format-id id "ud:~a" id))
       (with-syntax ([(ud:prim ...) (map make-prim-id (attribute prim-name))])
         #`(begin
             (define (id? id) (member id (list #'ud:prim ...) free-identifier=?))
             ;; Unfortunately, the nominal-source-id from calling
             ;; identifier-bindings with a prim identifier x
             ;; (i.e. (id? x) is true) was the ud:prim form and not
             ;; the prim-name form. So instead we have to build our
             ;; own approximation of what identifier-bindings does
             (define (id->user-sym prim-id)
               (define syms `((,#'ud:prim ,'prim-name) ...))
               (match (assoc prim-id syms free-identifier=?)
                 [(list _ user-sym) user-sym]))
             (define ud:prim (prim prim-name #'ud:prim)) ...
             (provide (rename-out [ud:prim prim-name] ...))))]))
  ;; a prim is a function that, when applied to code arguments,
  ;; produces code for applying the prim to the contents of the code
  ;; arguments
  (struct prim (proc id)
    #:property prop:procedure (struct-field-index proc))
  (define-prims #:id?/name prim-id? #:id->user-sym/name prim-id->user-sym
    * + add1 sub1 cons car cdr cadr null? pair? zero? equal? eq? number? println)


  ;; A hack so we can print code values (i.e. stx for expressions) in
  ;; the way that we provide the language bindings. It works except
  ;; as mentioned below when given a prim-id?
  (define (replace-names/exp stx)
    (define (nominal-source-name id) (fourth (identifier-binding id)))

    (syntax-parse stx
      #:literals ([lambda ud:lambda]
                  [#%datum ud:datum]
                  [#%app ud:app]
                  [if ud:if]
                  [lift ud:lift]
                  [run ud:run]
                  [let ud:let]
                  [let* ud:let*])
      [(lambda rec (args ...) body)
       `(,(nominal-source-name #'lambda)
         ,(syntax-e #'rec)
         ,(map syntax-e (attribute args))
         ,(replace-names/exp #'body))]
      [(#%datum . rest) (syntax->datum #'rest)]
      [(#%app args ...) (map replace-names/exp (attribute args))]
      [(if e1 e2 e3) `(,(nominal-source-name #'if) ,@(map replace-names/exp (list #'e1 #'e2 #'e3)))]
      [(lift e) `(,(nominal-source-name #'lift) ,(replace-names/exp #'e))]
      [(run e1 e2) `(,(nominal-source-name #'run) ,@(map replace-names/exp (list #'e1 #'e2)))]
      [((~or (~and let (~bind [letx 'let]))
             (~and let* (~bind [letx 'let*])))
        ([x0 e0] ...) e)
       (match* ((attribute x0) (attribute e0))
         [((list x0s ...) (list e0s ...))
          `(,(attribute letx)
               (,@(for/list ([x0 x0s]
                             [e0 e0s])
                    `[,(syntax-e x0) ,(replace-names/exp e0)]))
             ,(replace-names/exp #'e))])]
      [x:id
       (if (prim-id? #'x)
           (prim-id->user-sym #'x)
           (syntax-e #'x))]
      [_ (syntax->datum this-syntax)]))


  (define-syntax (ud:lambda stx)
    (syntax-parse stx
      [(_ rec:id (x:id ...) e:expr)
       (with-syntax ([raw-rec (format-id #'rec "raw-~a" #'rec)])
         ;; A bit of a mess but it lets us use the normal Racket
         ;; calling convention and still replace the self-reference
         ;; with code
         #`(letrec ([raw-rec (lambda (rec x ...) e)]
                    [rec (liftable-proc
                          (procedure-rename
                           (lambda (x ...) (raw-rec rec x ...))
                           'rec)
                          raw-rec #'rec (syntax->list #'(x ...)) #'e)])
             rec))]))
  (struct liftable-proc (value raw-value rec args body)
    #:property prop:procedure (struct-field-index value))

  (define-syntax (ud:datum stx)
    (syntax-parse stx
      [(_ . d:boolean) #`(#%datum . d)]
      [(_ . d:number) #`(#%datum . d)]
      [(_ . d:id) #`(#%datum . d)]
      [(_) #`(#%datum)]
      [(_ a . b) #`(#%datum a . b)]))

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

  (define-syntax-rule (ud:if e1 e2 e3)
    (match e1
      [(code e)
       (match* (e2 e3)
         [((code e2*) (code e3*))
          (code #`(ud:if #,e #,e2* #,e3*))]
         [(v2 v3)
          (raise-arguments-error
           'lift
           "Expected both branches of an if expression to produce code"
           "test" (syntax->datum #'e1)
           "produced code" (syntax->datum e)
           "then branch" (syntax->datum #'e2)
           "produced" v2
           "else branch" (syntax->datum #'e3)
           "produced" v3)])]
      [#f e3]
      [_ e2]))
  (define-syntax-rule (ud:if0 e1 e2 e3)
    ;; Tricky: need to expand to ud:app/ud:zero?
    (ud:if (ud:app ud:zero? e1) e2 e3))

  (define-syntax-rule (ud:lift e) (lift e))
  (define (lift v)
    (define v-exp
      (match v
        ;; Not clear if we should be traversing v in some way---before
        ;; I added booleans to ud:datum, I was able to lift '(#t). And
        ;; lifting cons like this is going to be buggy when there's
        ;; e.g. a function or code in the cons cell.
        [(? boolean? b) #`(ud:datum . #,b)]
        [(cons a b) #`(ud:datum #,a . #,b)]
        [(? number? n) #`(ud:datum . #,n)]
        [(? symbol? s) #`(ud:datum . #,s)]
        [(? null? s) #`(ud:datum)]
        [(liftable-proc proc raw-proc rec args _)
         (define rec-fresh (generate-temporary rec))
         (define args-fresh (generate-temporaries args))

         (match (apply raw-proc (code rec-fresh) (for/list ([a-f args-fresh]) (code a-f)))
           [(code e)
            #`(ud:lambda
               #,rec-fresh (#,@args-fresh)
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
    (when (print-eval?)
      (pretty-display "evaluating ")
      (pretty-print (syntax->datum e)))
    (define result (eval e (eval-namespace)))
    (when (print-eval?)
      (match result
        [(? liftable-proc? p)
         (pretty-display "produced proc with body ")
         (pretty-print (syntax->datum (liftable-proc-body p)))]
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

  (define-syntax (ud:define stx)
    (let ([error-msg/#f
           (match (syntax-local-context)
             ['expression "Definitions in expression contexts are not allowed"]
             [(cons _ _) "Internal definitions are not allowed"]
             [_ #f])])
      (when error-msg/#f (raise-syntax-error #f error-msg/#f stx)))

    (define-syntax-class curried-function-signature/rev
      #:attributes [fname idss-rev]
      (pattern (fname:id arg:id ...)
               #:attr idss-rev (list (attribute arg)))
      (pattern (sub:curried-function-signature/rev arg:id ...)
               #:attr fname (attribute sub.fname)
               #:attr idss-rev (cons (attribute arg) (attribute sub.idss-rev))))
    (define-syntax-class curried-function-signature
      #:attributes [fname idss]
      (pattern :curried-function-signature/rev
               #:attr idss (reverse (attribute idss-rev))))

    (syntax-parse stx
      [(_ sig:curried-function-signature e)
       ;; I only want define at a module body for now, and this should
       ;; be a hacky way to raise *some* error if define is used
       ;; outside of that..
       #`(define sig.fname
           (ud:lambda
            ;; Maybe we drop the self-reference from ud:lambda now
            ;; that we have define.
            sig.fname (#,@(car (attribute sig.idss)))
            #,(let loop ([idss (cdr (attribute sig.idss))])
                (if (null? idss)
                    #'e
                    #`(ud:lambda
                       _ (#,@(car idss))
                       #,(loop (cdr idss)))))))]
      [(_ x:id e) #`(define x e)]))

  (define reference-for-eval (#%variable-reference))
  (define eval-namespace (make-parameter #f))
  (define-syntax (ud:module-begin stx)
    (syntax-parse stx
      [(_ forms ...+)
       #`(#%module-begin
          (define updown-mp (variable-reference->resolved-module-path reference-for-eval))
          ;; Avoid parameterize around the module body because I don't
          ;; know a way for that to work w/printing-module-begin
          (let ([ns (make-base-empty-namespace)])
            ;; Use namespace-attach-module because we need to share
            ;; the eval-namespace parameter (or something like that,
            ;; see https://goo.gl/ihKPSH)
            (namespace-attach-module (current-namespace) updown-mp ns)
            (parameterize ([current-namespace ns])
              (namespace-require updown-mp))
            (eval-namespace ns))
          forms ...)]))
  (define-syntax-rule (check-code? e)
    (check-pred code? e))

  ;; Creates a letx form using the internal id, which expands to
  ;; Racket's binding for rktid; provides the forms as rktid
  (define-syntax (make-letx stx)
    (syntax-parse stx
      [(_ [internal:id rktid:id])
       (with-syntax ([ooo (quote-syntax ...)])
         #`(begin
             (define-syntax (internal stx)
               (syntax-parse stx
                 [(_ ([x0 e0] ooo) e)
                  (with-syntax ([(e0* ooo) (generate-temporaries (attribute e0))]
                                [(e*) (generate-temporaries (list #'e))])
                    #`(rktid ([x0 e0] ooo)
                             (match* (x0 ooo e)
                               [((code e0*) ooo (code e*))
                                (code #`(internal ([x0 #,e0*] ooo) #,e*))]
                               [(e0* ooo e*)
                                e*])))]))
             (provide (rename-out [internal rktid]))))]))
  ;; Make sure to update replace-names/exp, too
  (make-letx [ud:let let])
  (make-letx [ud:let* let*]))

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
   42)

  (check-code? (lift '(1 . 2)))
  (check-equal? (run 0 (lift '(1 . 2))) '(1 . 2))
  (check-code? (lift '(1 2)))
  (check-equal? (run 0 (lift (cons 1 (cons 2 '())))) '(1 2))

  (check-code? (lift 'a))
  (check-equal? (run 0 (lift 'a)) 'a)
  (check-equal? (run 0 (lift '((a 1) (b 2) (c 3)))) '((a 1) (b 2) (c 3)))

  (check-code? (lift #t))
  (check-equal? (run 0 (lift #f)) #f)
  (check-equal? (run 0 (lift '(#t #f))) '(#t #f))

  ;; This is the tiny matcher from the paper.
  (define ((matches? r) s)
    (if (null? r)
        #t
        (if (null? s)
            #f
            (if (eq? (car r) (car s))
                ((matches? (cdr r)) (cdr s))
                #f))))
  (check-true ((matches? '(a b)) '(a b c)))

  ;; This is the paper's lift-ready matcher. If you forget to lift any
  ;; of these places, the error messages are unpleasant.
  ;;
  ;; I don't yet do any let insertion, so if you trace-eval you see
  ;; cdr applied to to s twice in the resulting code:
  ;; - once for (null? (cdr s))
  ;; - once for (car (cdr s))
  (define ((matches?-spec r) s)
    (if (null? r)
        (lift #t)
        (if (null? s)
            (lift #f)
            (if (eq? (lift (car r)) (car s))
                ((matches?-spec (cdr r)) (cdr s))
                (lift #f)))))
  (check-true ((run 0 (lift (matches?-spec '(a b)))) '(a b c)))

  ;; More than just unary functions
  (define (k-#t) (super-equal? 10 10))
  (define (super-equal? x y) (equal? (equal? x y) (equal? y x)))
  (check-true (k-#t))
  (check-code? (lift super-equal?))

  (check-equal? (let ([n 13]) (add1 n)) 14)
  (check-equal? (let ([x 0] [y 1]) (+ x y)) 1)
  (check-equal? (let* ([x 0] [x (add1 x)]) x) 1)
  (check-code? (let ([n (lift 13)]) (add1 n)))
  (check-code? (let* ([x (lift 0)] [x (add1 x)]) x))
  (check-equal? (run 0 (let ([n (lift 13)]) (add1 n))) 14)

  (define x 10)
  (check-equal? x 10)
  (check-equal? ((lambda _ (y) (add1 x)) 0) 11))
