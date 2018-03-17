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
      (let* ([e1 (inc-e e)]
             [eval-e1 (eval e1)]
             [ret (add1 count)])
        (eval-e1 ret))
      (if (dec? e)
          (let* ([e1 (dec-e e)]
                 [eval-e1 (eval e1)]
                 [ret (sub1 count)])
            (eval-e1 ret))
          (if (mult? e)
              (let* ([e1 (mult-e1 e)]
                     [eval-e1 (eval e1)]
                     [v1 (eval-e1 count)]
                     [e2 (mult-e2 e)]
                     [ret (* v1 count)]
                     [eval-e2 (eval e2)])
                (eval-e2 ret))
              count))))

(module+ test
  (define mixed-exp '(add1 (add1 (sub1 (sub1 (sub1 ret))))))
  (check-equal? ((eval mixed-exp) 10) 9)
  (check-equal? ((run 0 (lift (eval mixed-exp))) 10) 9)

  (define mult-exp '(mult (add1 (add1 (add1 ret)))
                          ret))
  (check-equal? ((eval mult-exp) 1) 4)
  (check-equal? ((run 0 (lift (eval mult-exp))) 1) 4))
