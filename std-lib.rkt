#lang racket

(provide (all-defined-out))

(require "types.rkt"
         syntax/parse/define
         (for-syntax syntax/stx
                     racket/syntax
                     racket/list))

(begin-for-syntax
  (define PREFIXES '((Nano 10.0e-9)
                     (Micro 10.0e-6)
                     (Milli 10.0e-3)
                     (Centi 10.0e-2)
                     (Deci 10.0e-1)
                     (Kilo 10.0e3)
                     (Mega 10.0e6)
                     (Giga 10.0e9))))

(define-syntax-parse-rule (define-prefixed-unit U:id (~datum :) M:id)
  #:with ((prefixed-name factor) ...) (stx-map (lambda (p) (list (format-id #'U "~a~a" (first p) #'U)
                                                                 (datum->syntax #'U (second p))))
                                               PREFIXES)
  (begin
    (define-unit U : M)
    (define-unit prefixed-name = factor * U)
    ...))

(define-measure Distance)
(define-measure Time)

(define-prefixed-unit Meters : Distance)

(define-unit Feet = 0.3048 * Meters)

(define-unit Yards = 3 * Feet)

(define-unit Inches = 1/12 * Feet)

(define-prefixed-unit Seconds : Time)

(define-unit Minutes = 60.0 * Seconds)

(define-unit Hours = 60.0 * Minutes)
