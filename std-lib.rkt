#lang racket

(provide (all-defined-out))

(require "types.rkt")

(define-measure Distance)
(define-measure Time)

(define-unit Meters : Distance)

(define-unit Kilometers = 1000.0 * Meters)

(define-unit Feet = 0.3048 * Meters)

(define-unit Yards = 3 * Feet)

(define-unit Inches = 1/12 * Feet)

(define-unit Seconds : Time)

(define-unit Minutes = 60.0 * Seconds)

(define-unit Hours = 60.0 * Minutes)
