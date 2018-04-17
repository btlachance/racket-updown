#lang s-exp (submod "racket-updown.rkt" updown)
(define (eval-poly maybe-lift eval exp env)
  (if (number? exp) (maybe-lift exp)
  (if (symbol? exp) (env exp)
  (if (symbol? (car exp))
      (let ([rator (car exp)])
        (if (eq? 'lambda rator)
            (let* ([self (cadr exp)]
                   [formal (car (caddr exp))]
                   [body (cadddr exp)]
                   [f (lambda f (x)
                              (let ([env* (lambda (y) (if (eq? y self)
                                                          f
                                                          (if (eq? y formal)
                                                              x
                                                              (env y))))])
                                (eval body env*)))])
              (maybe-lift f))
        (if (eq? '+ rator) (+ (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? '- rator) (- (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? '* rator) (* (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? 'eq? rator) (eq? (eval (cadr exp) env) (eval (caddr exp) env))
        (if (eq? 'if rator) (if (eval (cadr exp) env)
                                (eval (caddr exp) env)
                                (eval (cadddr exp) env))
        ((env rator) (eval (cadr exp) env)))))))))
      (let ([rator (eval (car exp) env)]
            [rand (eval (cadr exp) env)])
        (rator rand))))))

(define (eval0 exp env) (eval-poly (lambda (v) v) eval0 exp env))
(define (eval exp) (eval0 exp (lambda (x) ('unbound x))))
(module+ test
  (check-equal? (eval '(+ 40 2)) 42)
  (check-equal? (eval '(- 5 7)) -2)
  (check-equal? (eval '(if (eq? 0 0) 1 0)) 1)
  (check-equal? (eval '(if (eq? 0 0) 0 1)) 0)

  (define fac-src '(lambda f (n) (if (eq? n 0) 1 (* n (f (- n 1))))))
  (check-equal? ((eval fac-src) 4) 24))

(define (evalc0 exp env) (eval-poly (lambda (v) (lift v)) evalc0 exp env))
(define (evalc exp) (evalc0 exp (lambda (x) ('unbound x))))
(module+ test
  (check-equal? ((run 0 (evalc fac-src)) 4) 24))
