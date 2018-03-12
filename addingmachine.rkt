#lang s-exp (submod "racket-updown.rkt" updown)

;; An e is one of
;; - ret
;; - `(add1 ,e)
;; - `(sub1 ,e)
;; - `(mult ,e1 ,e2)
(define (tag e) (car e))

(define (inc? e)
  (if (pair? e)
      (equal? 'add1 (tag e))
      #f))
(define (inc-e e) (cadr e))

(define (dec? e)
  (if (pair? e)
      (equal? 'sub1 (tag e))
      #f))
(define (dec-e e) (cadr e))

(define (mult? e)
  (if (pair? e)
      (equal? 'mult (tag e))
      #f))
(define (mult-e1 e) (cadr e))
(define (mult-e2 e) (caddr e))
(define (caddr v) (car (cdr (cdr v))))

(define ((eval e) count)
  (if (inc? e)
      ((eval (inc-e e)) (add1 count))
      (if (dec? e)
          ((eval (dec-e e)) (sub1 count))
          (if (mult? e)
              ;; It's a weird semantics where other operations
              ;; accumulate onto count but mult doesn't.. but this
              ;; will do for now.
              (let ([v1 ((eval (mult-e1 e)) count)])
                (let ([v2 ((eval (mult-e2 e)) count)])
                  (* v1 v2)))
              count))))

(module+ test
  (define mixed-exp '(add1 (add1 (sub1 (sub1 (sub1 ret))))))
  (check-equal? ((eval mixed-exp) 10) 9)
  (check-equal? ((run 0 (lift (eval mixed-exp))) 10) 9)

  (define mult-exp '(mult (add1 (add1 (add1 ret)))
                          (add1 (sub1 (add1 (sub1 ret))))))
  (check-equal? ((eval mult-exp) 0) 0)
  (check-equal? ((run 0 (lift (eval mult-exp))) 0) 0))
