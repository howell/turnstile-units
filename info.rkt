#lang info

;; Package metadata
(define collection "units")
(define version "0.1.0")

;; Dependencies
(define deps '("base"
               "turnstile-lib"))

;; Build dependencies (for testing)
(define build-deps '("rackunit-lib"))

;; Package description
(define pkg-desc "A DSL for dimensional analysis and unit conversions, implemented with Turnstile")

;; Authors
(define pkg-authors '())
