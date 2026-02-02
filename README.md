# Units Lang

This repo contains a prototype for a language supporting typed units of measure
and automatic conversions when performing arithmetic. The basic idea is to do
things like this:

```rkt
(define-measure Mass)
(define-unit Pounds : Mass)
(define-unit Killograms = 0.453592 * Pounds)

(print (+ (:: 8 Pounds) (:: 4 Killograms)))
;; => 21.63699536147022 :: Killograms
```

One of the key features is that no measurements or units are baked into the
language itself. The core system is completely agnostic and extensible; user
code defines all measurements, units, and conversions between them. One caveat,
though, is that currently only conversions via a scale factor are supported :-).

Naturally, conversions automatically lift over higher dimensions:

```rkt
(define falling (:: 9.8 (/ Meters (* Seconds Seconds))))
(define wind-resistance (:: 3 (/ Feet (* Minutes Minutes))))
;; the current system always uses the second arg as the returned unit
;; so specify that we want M/S²
(print (as (- falling wind-resistance)
           (/ Meters (* Seconds Seconds))))
;; => 9.799746 :: (/ Meters (* Seconds Seconds))
```

## Additional Features:
- Abstraction over units plus local type inference for calling polymorphic functions
  - unit abstraction implemented by typeclass-style dictionary-passing

```rkt
;; Compute distance traveled where the inital position, speed, and given time
;; can be in any unit:
(define (update-position [D :: Distance] [initial-position : (Num D)])
  (lambda ([D2 :: Distance] [T :: Time] [speed : (Num (/ D2 T))])
    (lambda ([T2 :: Time] [elapsed-time : (Num T2)])
      (+ initial-position (* speed elapsed-time)))))

;; No need to explictly specify D, D2, T, or T2; local inference solves for them
(define updater (update-position (:: 0 Meters)))
(define velocity-updater (updater (:: 5 (/ KiloMeters Hours))))
(print (velocity-updater (:: 10 Seconds)))
;; => 0.01388888888888889 :: KiloMeters
(print (velocity-updater (:: 10 Hours)))
;; => 50 :: KiloMeters
```

- Extensibility
This is a bit of a freebie with using Racket/Turnstile, but the code to define
`Meters`/`KiloMeters`/`MilliMeters` all together lives in *user space*:

```rkt
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
```
