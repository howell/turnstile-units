#lang units

(require units/std-lib)

#;(require "../types.rkt"
         "../std-lib.rkt")

(define (add-10m [U :: Distance] [d : (Num U)])
  (+ (:: 10 Meters) d))


(print (add-10m (:: 5 KiloMeters)))

#;(add-10m (:: 1 Seconds))

;; Three-level nested polymorphic lambdas:
(define (update-position [D :: Distance] [initial-position : (Num D)])
  (lambda ([D2 :: Distance] [T :: Time] [speed : (Num (/ D2 T))])
    (lambda ([T2 :: Time] [elapsed-time : (Num T2)])
      (+ initial-position (* speed elapsed-time)))))

(define updater (update-position (:: 0 Meters)))
(print updater)
(define velocity-updater (updater (:: 5 (/ KiloMeters Hours))))
(print (velocity-updater (:: 10 Seconds)))
(print (velocity-updater (:: 10 Hours)))
