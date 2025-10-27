#lang racket

(provide make-type-map
         type-map-ref
         type-map-set
         type-map-update
         type-map-keys
         type-map-remove
         type-map-find&remove
         type-map-find/key
         type-map-combine
         type-map-equal/in-order?
         type-map-map-entries
         type-map-map-values
         type-map-map*
         type-map-filter
         in-type-map)

(require (for-meta -1 turnstile/base))

#|
An associative data structure with types as keys
|#

(define (make-type-map) '())

;; (TypeMap A) Type -> (Optionof A)
(define (type-map-ref tm t [failure-result #f])
  (match (assoc t tm type=?)
    [#f
     (if (procedure? failure-result)
         (failure-result)
         failure-result)]
    [entry
     (cdr entry)]))

;; (TypeMap A) Type A -> (TypeMap A)
(define (type-map-set tm t v)
  (define-values (hd tl) (splitf-at tm
                                    (lambda (entry) (not (type=? t (car entry))))))
  (append hd
          (list (cons t v))
          (if (null? tl)
              tl
              (cdr tl))))

;; (TypeMap A) Type (A -> A) -> (TypeMap A)
(define (type-map-update tm t updater [failure-result #f])
  (define-values (hd tl) (splitf-at tm
                                    (lambda (entry) (not (type=? t (car entry))))))
  (define-values (base-v new-tl)
    (match tl
      ['()
       (define v (if (procedure? failure-result)
                     (failure-result)
                     failure-result))
       (values v '())]
      [(cons (cons _ v) rst)
       (values v rst)]))
  (append hd
          (list (cons t (updater base-v)))
          new-tl))

;; (TypeMap A) -> (Listof Type)
(define (type-map-keys tm)
  (map car tm))

;; (TypeMap A) Type -> (TypeMap A)
(define (type-map-remove tm t)
  (remove t tm (lambda (_t entry) (type=? t (car entry)))))

;; (TypeMap A) Type -> (Values (TypeMap A) (Optionof (Cons Type A)))
(define (type-map-find&remove tm t)
  (define-values (hd tl) (splitf-at tm
                                    (lambda (entry) (not (type=? t (car entry))))))
  (if (null? tl)
      (values tm #f)
      (values (append hd (cdr tl))
              (car tl))))

;; (TypeMap A) {Type -> Bool} -> (Optionof (Cons Type A))
(define (type-map-find/key tm pred)
  (for/first ([entry (in-list tm)]
              #:when (pred (car entry)))
    entry))

;; (TypeMap A) (TypeMap B) {A B -> (U A B)} -> (TypeMap (U A B))
(define (type-map-combine tm1 tm2 combiner)
  (for/fold ([res tm2])
            ([entry (in-list tm1)])
    (define-values (res* e2) (type-map-find&remove res (car entry)))
    (define v
      (if e2
          (combiner (cdr entry) (cdr e2))
          (cdr entry)))
    (cons (cons (car entry) v)
          res*)))

;; (TypeMap A) (TypeMap A) -> Bool
(define (type-map-equal/in-order? tm1 tm2)
  (and (= (length tm1) (length tm2))
       (andmap (lambda (e1 e2) (and (type=? (car e1) (car e2))
                                    (equal? (cdr e1) (cdr e2))))
               tm1
               tm2)))

;; (TypeMap A) {Type A -> B} -> (Listof B)
(define (type-map-map-entries tm proc)
  (map (lambda (e) (proc (car e) (cdr e)))
       tm))

;; (TypeMap A) {Type A -> Bool} -> (TypeMap A)
(define (type-map-filter tm pred)
  (filter (lambda (e) (pred (car e) (cdr e)))
          tm))

(define (type-map-map* proc . tms)
  (apply map proc tms))

(define (type-map-map-values proc tm)
  (map (lambda (entry) (cons (car entry) (proc (cdr entry))))
       tm))

(define (in-type-map tm)
  (make-do-sequence
   (lambda ()
     (initiate-sequence #:pos->element (lambda (tm) (values (caar tm) (cdar tm)))
                        #:next-pos cdr
                        #:init-pos tm
                        #:continue-with-pos? cons?))))
