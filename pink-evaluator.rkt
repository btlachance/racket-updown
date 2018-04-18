#lang s-exp (submod "racket-updown.rkt" updown)
(define ((mk/eval-poly lookup extend) maybe-lift eval exp env)
  (if (number? exp) (maybe-lift exp)
  (if (symbol? exp) (lookup exp env)
  (if (symbol? (car exp))
      (let ([rator (car exp)])
        (if (eq? 'lambda rator)
            (let* ([self (cadr exp)]
                   [formal (car (caddr exp))]
                   [body (cadddr exp)]
                   [f (lambda f (x)
                        (let ([env* (extend self f (extend formal x env))])
                          (eval body env*)))])
              (maybe-lift f))
        (if (eq? '+ rator) (+ (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? '- rator) (- (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? '* rator) (* (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? 'eq? rator) (eq? (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? 'if rator) (if (eval (cadr exp) env)
                                (eval (caddr exp) env)
                                (eval (cadddr exp) env))
        ((lookup rator env) (eval (cadr exp) env)))))))))
      (let ([rator (eval (car exp) env)]
            [rand (eval (cadr exp) env)])
        (rator rand))))))

(define emptyenv/d '())
(define (lookup/d x env)
  (if (null? env)
      ('unbound x)
      (let ([y (car env)]
            [v (cadr env)]
            [env-rest (cdr (cdr env))])
        (if (eq? x y)
            v
            (lookup/d x env-rest)))))
(define (extend/d x v env)
  (cons x (cons v env)))

(define emptyenv/f (lambda (x) ('unbound x)))
(define (lookup/f x env) (env x))
(define (extend/f x v env) (lambda (y) (if (eq? x y) v (lookup/f y env))))
(module+ test
  (define env0 (extend/f 'x 0 emptyenv/f))
  (check-equal? (lookup/f 'x env0) 0)

  (define env1 (extend/f 'y 1 env0))
  (check-equal? (lookup/f 'y env1) 1)
  (check-equal? (lookup/f 'x env1) 0))

(define (mk/eval lookup extend emptyenv)
  (let* ([eval-poly (mk/eval-poly lookup extend)]
         [eval (lambda eval (exp env) (eval-poly (lambda (v) v) eval exp env))])
    (lambda (exp) (eval exp emptyenv))))
(define (mk/evalc lookup extend emptyenv)
  (let* ([eval-poly (mk/eval-poly lookup extend)]
         [evalc (lambda evalc (exp env) (eval-poly (lambda (v) (lift v)) evalc exp env))])
    (lambda (exp) (evalc exp emptyenv))))

(define eval/d (mk/eval lookup/d extend/d emptyenv/d))
(define eval/f (mk/eval lookup/f extend/f emptyenv/f))
(module+ test
  (check-equal? (eval/f '(+ 40 2)) 42)
  (check-equal? (eval/f '(- 5 7)) -2)

  (check-equal? (eval/f '(if (eq? 0 0) 1 0)) 1)
  (check-equal? (eval/f '(if (eq? 0 0) 0 1)) 0)

  (define id-src '(lambda _ (x) x))
  (check-equal? ((eval/f id-src) 10) 10)

  (define fac-src '(lambda fac (n) (if (eq? n 0) 1 (* n (fac (- n 1))))))
  (check-equal? ((eval/f fac-src) 4) 24)
  (check-equal? ((eval/d fac-src) 4) 24))

(define evalc/d (mk/evalc lookup/d extend/d emptyenv/d))
(define evalc/f (mk/evalc lookup/f extend/f emptyenv/f))
(module+ test
  (check-equal? ((run 0 (evalc/d fac-src)) 4) 24)
  (check-equal? ((run 0 (evalc/f fac-src)) 4) 24))
