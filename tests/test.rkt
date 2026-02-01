#lang units

#;(require "../types.rkt")

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

(define position (:: 3 Kilometers))
(define speed (:: 10 (/ Yards Seconds)))
(define elapsed-time (:: 12 Minutes))

(print (+ position (* speed elapsed-time)))
;; => 10480.839895013123 :: Yards ~ Yards

#;(print (:: 5 Meters))

#|
(print Distance)
(print Meters)
(print (* Meters Meters))
(print (:: 10 (* Meters Meters)))
(print (* Distance Distance))

|#
(print (+ (:: 50 Meters)
          (:: 5 Meters)))

#;(print (+ (:: 1 Kilometers)
          (:: 5 Meters)))

#;(print (+ (:: 2 Yards)
            (:: 1 Feet)))

#;(print (:: 2 (* Yards Yards)))

(print (+ (:: 2 (* Yards Yards))
          (:: 1 (* Feet Feet))))

(print (+ (:: 1 (/ Meters Seconds))
            (:: 1 (/ Kilometers Minutes))))

(print (:: 5 (/ 1 Seconds)))

(print (/ Meters Seconds))

;; should give an error
#;(print (+ (:: 50 Meters)
            (:: 5 Seconds)))

#;(print Kilometers)

#;(print Distance)

(print (* (:: 5 Meters) (:: 10 (* Meters Meters))))
(print (* (:: 100 (* Meters Minutes))
          (:: 10 (/ Kilometers Seconds))))

#;(print
 (+ (:: 3 Kilometers) ;; current position
    (* (:: 10 (/ Yards Seconds)) ;; current speed
       (:: 12 Minutes))) ;; time elapsed
 )

#|
(* Distance Distance) => (Prod Distance Distance)
(* Meters Meters) => (Prod Meters Meters)
|#

(print (/ (:: 10 Meters)
          (:: 2 Seconds)))

(print (/ (:: 1 Meters)
          (:: 1 (* Kilometers Kilometers))))

(print (+ (/ (:: 10 Meters)
             (:: 2 Seconds))
          (/ (:: 10 Meters)
             (:: 2 Seconds))))

(print (+ (/ (:: 10 Meters)
             (:: 2 Seconds))
          (/ (:: 1 Kilometers)
             (:: 2 Seconds))))


(print (- (:: 1 Yards) (:: 1 Feet)))
