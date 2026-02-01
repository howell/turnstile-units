#lang units

(require units/std-lib)

;; Simple nested lambda - outer returns a function
(define (make-adder [U :: Distance] [x : (Num U)])
  (lambda ([y : (Num U)])
    (+ x y)))

(define add-meters (make-adder (:: 5 Meters)))
(print (add-meters (:: 2 Meters)))
(print (add-meters (:: 10 Meters)))
