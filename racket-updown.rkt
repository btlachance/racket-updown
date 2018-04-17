#lang racket
(module updown racket
  (require (for-syntax syntax/parse racket/syntax racket/match racket/pretty)
           syntax/wrap-modbeg
           syntax/parse
           racket/syntax
           racket/struct
           rackunit)
  (provide trace-eval
           check-equal?
           check-true
           check-code?
           module+
           begin
           let
           let*
           (rename-out [ud:module-begin #%module-begin]
                       [ud:top-interaction #%top-interaction]
                       [ud:lambda lambda]
                       [ud:app #%app]
                       [ud:datum #%datum]
                       [ud:if0 if0]
                       [ud:if if]
                       [ud:lift lift]
                       [ud:run run]
                       [ud:define define]
                       [ud:quote quote]
                       #;(Make sure to update replace-names/exp, too)))

  (struct code (e)
    #:property prop:procedure
    (lambda (c . args)
      (if (andmap code? args)
          (code (reflect-exp (apply exp-for-app c args)))
          (error 'foo)))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (lambda (c) 'code)
        (lambda (c) (list (replace-names/exp (code-e c))))))])

  (struct binding (id exp) #:transparent)
  (define reflected (make-parameter '()))
  (define (reflect-exp exp)
    (define tmp (generate-temporary))
    (reflected (cons (binding tmp exp) (reflected)))
    tmp)
  (define (output-reflecteds reflected-bindings body)
    ;; Don't output (let* ([x0 e0] ...+ [x e]) x); instead, simplify
    ;; that to (let* ([x0 e0] ...+) e)
    (define-values (reflected-bindings* body*)
      (match reflected-bindings
        [(list) (values reflected-bindings body)]
        [(cons newest-b bs)
         (if (and (identifier? body) (free-identifier=? (binding-id newest-b) body))
             (values bs (binding-exp newest-b))
             (values reflected-bindings body))]))

    (define bindings
      (map
       (lambda (b) #`[#,(binding-id b) #,(binding-exp b)])
       (reverse reflected-bindings*)))
    (match bindings
      [(list) body*]
      [(list bs ...)
       #`(let* #,bs #,body*)]))
  (define (reify-for-code/unwrap thunk)
    (parameterize ([reflected '()])
      (match* ((thunk) (reflected))
        [((code e) (list reflecteds ...))
         (output-reflecteds reflecteds e)])))
  (define (reifyv thunk #:ignore-when-void? [ignore-void? #f])
    (parameterize ([reflected '()])
      (match* ((thunk) (reflected))
        [(v (list)) v]

        ;; Used for module body/#%top-interaction
        [((? void? _) bindings)
         #:when ignore-void?
         (void)]

        [((code e) (list reflecteds ...))
         (code (output-reflecteds reflecteds e))])))

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
             (define (make-prim-proc prim ud:prim/thunk)
               (lambda args
                 (if (andmap code? args)
                     (code (reflect-exp (apply exp-for-app (ud:prim/thunk) args)))
                     (apply prim args))))
             (define ud:prim (prim (make-prim-proc prim-name (lambda () ud:prim)) #'ud:prim)) ...
             (provide (rename-out [ud:prim prim-name] ...))))]))
  ;; a prim is a function that, when applied to code arguments,
  ;; produces code for applying the prim to the contents of the code
  ;; arguments
  (struct prim (proc id)
    #:property prop:procedure (struct-field-index proc))
  (define-prims #:id?/name prim-id? #:id->user-sym/name prim-id->user-sym
    * + - add1 sub1 cons car cdr cadr caddr cadddr null? pair?
    zero? equal? eq? number? symbol? println not list)


  ;; A hack so we can print code values (i.e. stx for expressions) in
  ;; the way that we provide the language bindings. It's mostly
  ;; reusing Racket's knowledge of the identifiers, expect for the
  ;; prim-id's---identifier-binding for some reason gives back a
  ;; nominal-source-id and source-id that are both of the form ud:x
  (define (replace-names/exp stx)
    (define (nominal-source-name id) (fourth (identifier-binding id)))

    (syntax-parse stx
      #:literals ([lambda ud:lambda]
                  [#%datum ud:datum]
                  [#%app ud:app]
                  [if ud:if]
                  [lift ud:lift]
                  [run ud:run]
                  ;; what about ud:quote/quote?
                  let
                  let*)
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
      [((~and form (~or let let*))
        ([x0 e0] ...) e)
       (match* ((attribute x0) (attribute e0))
         [((list x0s ...) (list e0s ...))
          `(,(syntax-e #'form)
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
      [(_ (x:id ...) e)
       #`(let* ([raw-proc (lambda (_ x ...) e)]
                [proc (liftable-proc
                       (lambda (x ...) (raw-proc (void) x ...))
                       raw-proc
                       #f
                       (syntax->list #'(x ...))
                       #'e)])
           proc)]
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
      [(_ . d) #`(#%datum . d)]))
  (define-syntax (ud:quote stx)
    (syntax-parse stx
      [(_ (a . b)) #`(ud:app ud:cons (ud:quote a) (ud:quote b))]
      [(_ s) #`(ud:datum . s)]))

  (define (exp-for-app rator . rands)
    (define rator-stx
      (if (prim? rator)
          (prim-id rator)
          (code-e rator)))
    #`(ud:app #,rator-stx #,@(map code-e rands)))

  (define-syntax (ud:app stx)
    (syntax-parse stx
      [(_ rator rands ...) #`(#%app rator rands ...)]))

  (begin-for-syntax
    (define-syntax-class with-binding
      #:attributes (exp binding)
      (pattern :atomic
               #:attr exp this-syntax
               #:attr binding #f)
      (pattern e
               #:attr exp (generate-temporary #'e)
               #:attr binding #`[exp e]))
    (define-syntax-class atomic
      (pattern :id)
      (pattern :boolean)
      (pattern :number)))
  (define-syntax (ud:if stx)
    (syntax-parse stx
      [(_ test:atomic then else)
       #`(if (code? test)
             (code (exp-for-if test (thunk then) (thunk else)))
             (if test
                 then
                 else))]
      [(_ test:with-binding then else)
       (if (attribute test.binding)
           #`(let (test.binding)
               (ud:if test.exp then else))
           #`(ud:if test.exp then else))]))
  (define (exp-for-if test then-thunk else-thunk)
    #`(ud:if #,(code-e test)
             #,(reify-for-code/unwrap then-thunk)
             #,(reify-for-code/unwrap else-thunk)))

  (define-syntax-rule (ud:if0 e1 e2 e3)
    ;; Tricky: need to expand to ud:app/ud:zero?
    (ud:if (ud:app ud:zero? e1) e2 e3))

  (define-syntax-rule (ud:lift e) (lift e))
  (define (lift v)
    (define v-exp
      (match v
        [(? boolean? b) b]
        [(cons a b)
         (define (unpack-code v)
           (match v
             [(code e)
              (syntax-parse e
                #:literals (quote)
                [(quote i:id) (syntax-e #'i)]
                [_ this-syntax])]
             [(cons a* b*)
              (cons (unpack-code a*) (unpack-code b*))]
             [_ v]))
         #`(ud:datum #,(unpack-code a) . #,(unpack-code b))]
        [(? number? n) n]
        [(? symbol? s)
         ;; Symbols still feel weird. But this + the stuff with cons
         ;; above seems to do what I think I want. Unclear: why not
         ;; use ud:quote here? (Tests fail, but why?)
         #`(quote #,s)]
        [(? null? s) #`(ud:datum)]
        [(liftable-proc proc raw-proc rec args _)
         (define rec-fresh (generate-temporary rec))
         (define args-fresh (generate-temporaries args))

         #`(ud:lambda
            #,rec-fresh #,args-fresh
            #,(reify-for-code/unwrap (thunk (apply raw-proc (code rec-fresh) (for/list ([a-f args-fresh]) (code a-f))))))]
        [(prim _ id) id]
        [(code e) (reflect-exp #`(ud:lift #,e))]))
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
       (reifyv (thunk (eval-code-exp (reify-for-code/unwrap (thunk e)))))]))

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
                       (#,@(car idss))
                       #,(loop (cdr idss)))))))]
      [(_ x:id e) #`(define x e)]))

  (define-syntax (wrap-reifyv stx)
    (syntax-case stx ()
      ;; I'm not certain we can just ignore any bindings that get
      ;; accumulated because of e, but if the whole thing evaluates to
      ;; void then I don't see what else we could do with the
      ;; bindings.
      [(_ e) #'(reifyv (thunk e) #:ignore-when-void? #t)]))
  (define-syntax reifyv-module-begin (make-wrapping-module-begin #'wrap-reifyv #'#%printing-module-begin))

  (define reference-for-eval (#%variable-reference))
  (define eval-namespace (make-parameter #f))
  (define-syntax (ud:module-begin stx)
    (syntax-parse stx
      [(_ forms ...)
       #`(reifyv-module-begin
          (define updown-mp (variable-reference->resolved-module-path reference-for-eval))
          (define _
            ;; Avoid parameterize around the module body because I don't
            ;; know a way for that to work w/printing-module-begin
            (let ([ns (make-base-empty-namespace)])
              ;; Use namespace-attach-module because we need to share
              ;; the eval-namespace parameter (or something like that,
              ;; see https://goo.gl/ihKPSH)
              (namespace-attach-module (current-namespace) updown-mp ns)
              (parameterize ([current-namespace ns])
                (namespace-require updown-mp))
              (eval-namespace ns)))
          forms ...)]))
  (define-syntax (ud:top-interaction stx)
    (syntax-case stx ()
      [(_ . f) #'(wrap-reifyv f)]))
  (define-syntax-rule (check-code? e) (check-pred code? e)))

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
  (check-equal? (run 0 (lift '())) '())

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

  ;; A factorial function like the one in the paper's fig 7
  (check-code? (lift (lambda fac (n)
                             (if (not (zero? n))
                                 (* n (fac (sub1 n)))
                                 (lift 1)))))

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
  (check-equal? ((lambda _ (y) (add1 x)) 0) 11)

  ;; This one feels weird, but without it I'm otherwise not sure how
  ;; to represent small step states. Maybe I should be reifying the
  ;; lifted number/symbol...
  (define list-with-code (list 'state 'ret (lift 0) (lift 'kdone)))
  (check-equal? (run 0 (lift list-with-code)) '(state ret 0 kdone)))
