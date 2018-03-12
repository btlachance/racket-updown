#lang s-exp (submod "racket-updown.rkt" updown)
;; A small-step abstract machine for a very simple language.

;; An e is one of
;; - n
;; - `(add1 ,e)
(define (add? e)
  (if (pair? e)
      (eq? (car e) 'add1)
      #f))
(define (add-e e) (cadr e))

;; A k is one of
;; - 'done
;; - `(inc . ,k)
(define (inc k) (cons 'inc k))
(define (inc? k) (if (pair? k)
                     (eq? (car k) 'inc)
                     #f))
(define (inc-next k) (cdr k))

;; A state is a (cons e k)
(define (state e k) (cons e k))
(define (state-e s) (car s))
(define (state-k s) (cdr s))

(define (final-state? state)
  (if (eq? (state-k state) 'done)
      (number? (state-e state))
      #f))

;; step : e k -> state
(define (step e k)
  (if (add? e)
      (state (add-e e) (inc k))
      (if (inc? k)
          (step (add1 e) (inc-next k))
          ;; If there's no state to step to, just return the current
          ;; state
          (state e k))))

(define (run e)
  ((lambda run* (s)
           (if (final-state? s)
               (state-e s)
               (run* (step (state-e s) (state-k s)))))
   (state e 'done)))

(module+ test
  (check-equal? (run 5) 5)
  (check-equal? (run '(add1 (add1 (add1 3)))) 6))

;; If run is an evaluator, then I don't think there's much point in
;; applying it to some program and then lifting what comes out: when
;; applied to a program, it returns the program's result! In the
;; other evaluators we lifted a function, not the program's result.
;; This makes me think we need to lift step, somehow. So, for now,
;; I've curried it.
(define ((step-spec e) k)
  (if (add? e)
      (lift (state (add-e e) (inc k)))
      (lift
       (if (inc? k)
           (state (add1 e) (inc-next k))
           (state e k)))))
(module+ test
  ;; TODO this produces a function whose body is `(5 inc . ,code-for-k))
  ;; but we want just `(5 inc . ,k). When lifting a cons cell, in some
  ;; form or another we have to unwrap code that appears in a cons cell.
  (check-code? (lift (step-spec '(add1 5))))

  ;; Funny enough, this one is still giving me trouble. Because inc?
  ;; doesn't evaluate to a primitive or to code, the call to it with the
  ;; code argument for k doesn't do what we want; it just passes the
  ;; code along to inc?. And at that point things are murky (for
  ;; example, car in the body of inc? is never called).
  #;(check-code? (lift (step-spec '5))))
