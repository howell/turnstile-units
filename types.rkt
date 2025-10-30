#lang turnstile

(provide Measure
         Unit
         Num
         Prod Div
         define-measure
         define-unit
         ::
         * /
         +
         print
         define
         (for-syntax conversions))

(require (for-syntax "type-map.rkt")
         turnstile/typedefs)

(define-type Type : Type)

(define-type Measure : Measure)
(define-type UnitLike : UnitLike)
(define-type Unit : UnitLike)

(define-type Dimensionless : Measure
  #:implements get-resugar-info
  (lambda (_) #'1))

(define-for-syntax DIMENSIONLESS ((current-type-eval) #'Dimensionless))

(define-internal-type/new ProdInt- (ProdInt t1 t2)
  #:implements get-resugar-info
  (syntax-parser
    [(~ProdInt t1 t2)
     (list #'* (resugar-type #'t1) (resugar-type #'t2))]))

(define-internal-type/new DivInt- (DivInt t1 t2)
  #:implements get-resugar-info
  (syntax-parser
    [(~DivInt t1 t2)
     (list #'/ (resugar-type #'t1) (resugar-type #'t2))]))

(define-type ConversionConstraint : ConversionConstraint)
(define-type <~> : UnitLike UnitLike -> ConversionConstraint)
#;(define-internal-type/new ConversionConstraint- (ConversionConstraint u1 u2)
  #:implements get-resugar-info
  (syntax-parser
    [(~ConversionConstraint u1 u2)
     (list #'<~> (resugar-type #'u1) (resugar-type #'u2))]))

(define-type Num : UnitLike -> Type)

(define-type Conversions :
  Conversions)
(define-type ConversionConstraints : ConversionConstraint * -> Conversions
  #:implements get-resugar-info
  (syntax-parser
    [(~ConversionConstraints cs ...)
     (cons #'Constraints (stx-map resugar-type #'(cs ...)))]))

(define-type → : Conversions Type Type * -> Type)
(define-type Λ #:with-binders [X : UnitLike] : Type -> Type)

(define-syntax-parser Λ+
  [(_ () body)
   #'body]
  [(_ ([X:id (~optional (~datum ::)) Kind] tvs ...) body)
   (syntax/loc this-syntax
     (Λ (X : Kind) (Λ+ (tvs ...) body)))])

(begin-for-syntax
  (define (sequentialize-Λ-stx stx)
    (let loop ([bvs/rev '()])
      (syntax-parse stx
        [(~Λ [bv : k] body)
         (loop (cons #'(bv : k) bvs/rev)
               #'body)]
        [_
         #`(#,(reverse bvs/rev) stx)])))

  (define-for-syntax ~Λ+
    (pattern-expander
     (syntax-parser
       [(_ tvs-pat body-pat)
        #'(~or* (~and lam
                      (~Λ _ _)
                      (~parse (tvs-pat body-pat)
                              (sequentialize-Λ-stx #'lam)))
                (~and (~parse tvs-pat #'())
                      body-pat))])))
  )

(begin-for-syntax
  (define-syntax ~effs
    (pattern-expander
     (syntax-parser
       [(_ eff ...)
        #:with tmp (generate-temporary 'effss)
        #'(~and tmp
                (~parse (eff ...) (stx-or #'tmp #'())))])))

  (define (stx-truth? a)
    (and a (not (and (syntax? a) (false? (syntax-e a))))))
  (define (stx-or a b)
    (cond [(stx-truth? a) a]
          [else b])))

(begin-for-syntax
  (define (<: t1 t2)
    #;(printf "(<: ~a\n    ~a)\n" t1 t2)
    (syntax-e
     (syntax-parse/typecheck #`(#,t1 #,t2)
       [(t1 ~Unit)
        ≫
        #:cut
        [⊢ t1 ≫ _ ⇒ u1]
        [⊢ u1 ≫ _ ⇐ Measure]
        ---
        [≻ #t]]
       [(t1 ~UnitLike)
        ≫
        #:cut
        [⊢ t1 ≫ _ ⇐ Measure]
        ---
        [≻ #t]]
       [_
        ≫
        ---
        [≻ #,(type=? t1 t2)]])))

  (current-typecheck-relation <:)
  )


(define-typed-syntax Prod
  [(_ (~or* 1 ~Dimensionless) t)
   ≫
   --------------------
   [≻ t]]
  [(_ t (~or* 1 ~Dimensionless))
   ≫
   --------------------
   [≻ t]]
  [(_ t1 t2)
   ≫
   [⊢ t1 ≫ t1- (⇒ ~Measure)]
   [⊢ t2 ≫ t2- (⇒ ~Measure)]
   --------------------
   [⊢ (ProdInt- t1- t2-) (⇒ : Measure)]]
  [(_ t1 t2)
   ≫
   [⊢ t1 ≫ t1- ⇒ K1]
   [⊢ t2 ≫ t2- ⇒ K2]
   [⊢ K1 ≫ K1- ⇐ Measure]
   [⊢ K2 ≫ K2- ⇐ Measure]
   --------------------
   [⊢ (ProdInt- t1- t2-) ⇒ (Prod K1- K2-)]])

(define-typed-syntax Div
  [(_ 1 t)
   ≫
   --------------------
   [≻ (Div Dimensionless t)]]
  [(_ t (~or* 1 ~Dimensionless))
   ≫
   --------------------
   [≻ t]]
  [(_ t1 t2)
   ≫
   [⊢ t1 ≫ t1- (⇒ ~Measure)]
   [⊢ t2 ≫ t2- (⇒ ~Measure)]
   --------------------
   [⊢ (DivInt- t1- t2-) ⇒ Measure]]
  [(_ t1 t2)
   ≫
   [⊢ t1 ≫ t1- ⇒ K1]
   [⊢ t2 ≫ t2- ⇒ K2]
   [⊢ K1 ≫ K1- ⇐ Measure]
   [⊢ K2 ≫ K2- ⇐ Measure]
   --------------------
   [⊢ (DivInt- t1- t2-) ⇒ (Div K1- K2-)]])


(define-typed-syntax (define-measure M:id) ≫
  ---------------------
  [≻ (define-type M : Measure)])

(define-typed-syntax define-unit
  [(_ U (~datum :) M)
   ≫
   [⊢ M ≫ M- ⇒ ~Measure]
   ---------------------
   [≻ (define-type U : M-)]]
  [(_ U (~datum =) n:number (~datum *) U_base)
   ≫
   [⊢ U_base ≫ U_base- ⇒ M]
   [⊢ M ≫ M- ⇒ ~Measure]
   ---------------------
   [≻ (begin
        (define-type U : M-)
        (begin-for-syntax
          (record-factor-conversion! #'U #'U_base- n)))]])

(begin-for-syntax
  ;; A graph describing how to convert from one unit to another (of the same measure)
  ;; Represents the graph as adjacency lists, mapping a node (unit) to a map
  ;; of its neighbors and the method of converting to that neighbor
  (define conversions (make-type-map))

  (define (type-eval t) ((current-type-eval) t))

  (define (resugar* t)
    (define resugared (resugar-type t))
    (if (list? resugared)
        (map syntax->datum resugared)
        resugared))

  (define (record-edge! from to by)
    (define conversions*
      (type-map-update conversions
                       from
                       (lambda (edges) (type-map-set edges to by))
                       make-type-map))
    (set! conversions conversions*))

  ;; records the ability to convert from unit `u1` to unit `u2` by applying a constant factor `k`,
  ;; and vice versa by inverting `k`
  (define (record-factor-conversion! u1 u2 k)
    (define-values (u1- u2-) (values (type-eval u1) (type-eval u2)))
    (record-edge! u1- u2- k)
    (record-edge! u2- u1- (/ 1 k)))

  ;; Given two units of the same measure, determine a way to convert each to a common unit so that they may be added/compared/etc
  ;; Performs a BFS from `u1` to find the shortest path to `u2`
  ;; Returns
  ;;   - (Listof Number Number Unit), when successful describing the factor to apply to each input unit to yield a value of the returned unit
  ;;   - #f if no such conversion can be found
  (define (reconcile-units u1 u2)
    (define-values (u1- u2-) (values (type-eval u1) (type-eval u2)))
    (match (breadth-first-search conversions u1- u2-)
      [#f #f]
      [path
       #;(printf "path:\n~a\n" path)
       (define k (for/product ([pe (in-list path)]) (cdr pe)))
       (list k 1 u2)]))

  (define (breadth-first-search graph from to )
    (define (search paths seen)
      (match paths
        ['()
         #f]
        [(cons (and path (cons path-hd _)) rst)
         (match (type-map-ref graph (car path-hd))
           [#f
            (search rst seen)]
           [edges
            (match (type-map-ref edges to)
              [#f
               (define new-work
                 (for/list ([edge (in-list edges)]
                            #:unless (set-member? seen (car edge)))
                   (cons edge path)))
               (search (append rst new-work)
                       (set-union seen
                                  (for/set ([e (in-list edges)]) (car e))))]
              [v
               (cons (cons to v) path)])])]))

    (if (type=? from to)
        (list (cons from 1))
        (search (list (list (cons from 1))) (set from))))

  ;; Convert a unit/measure type to a normal form, mapping each base unit/measure to an exponent
  ;; Type -> (TypeMap Integer)
  (define (normalize t)
    (define expnts
      (let loop ([t t]
                 [tm (make-type-map)]
                 [sign 1])
        (syntax-parse t
          [(~ProdInt t1 t2)
           (loop #'t2
                 (loop #'t1 tm sign)
                 sign)]
          [(~DivInt t1 t2)
           (loop #'t2
                 (loop #'t1 tm sign)
                 (* -1 sign))]
          [~Dimensionless
           tm]
          [_
           (type-map-update tm t (lambda (n) (+ n sign)) 0)])))
    (define nonzeros (type-map-filter expnts (lambda (_k n) (not (zero? n)))))
    (sort nonzeros
          (lambda (x y) (string<=? (~a (syntax->datum x))
                                   (~a (syntax->datum y))))
          #:key car))

  ;; (TypeMap Integer) -> Type
  (define (denormalize tm)
    (for/fold ([res DIMENSIONLESS]
               #:result ((current-type-eval) res))
              ([(ty exponent) (in-type-map tm)])
      (define base (for/fold ([t ty])
                             ([_i (in-range 1 (abs exponent))])
                     #`(Prod #,ty #,t)))
      (cond
        [(zero? exponent)
         res]
        [(negative? exponent)
         #`(Div #,res #,base)]
        [else
         #`(Prod #,res #,base)])))

  (define (format-normalized n)
    (define (fmt ty exponent)
      (let* ([ty (resugar* ty)]
             [ty (if (syntax? ty)
                     (syntax->datum ty)
                     ty)])
        (if (= exponent 1)
            (~a ty)
            (format "~a^~a" ty exponent))))
    (string-join (type-map-map-entries n fmt)
                 "·"))


  (define (has-measure? t measure)
    (type=? (typeof t) measure))

  (define (find-by-measure tm measure)
    (type-map-find/key tm (lambda (t) (has-measure? t measure))))

  (define (bridge-units-of-common-measure measures units1 units2 #:src src-stx)
    (for/fold ([scale1 1]
               [scale2 1]
               [conversions '()]
               [result-units (make-type-map)])
              ([(measure measure-expt) (in-type-map measures)])
      (define entry1? (find-by-measure units1 measure))
      (define entry2? (find-by-measure units2 measure))
      (match* (entry1? entry2?)
        [((cons unit1 expt1) (cons unit2 expt2))
         (cond
           [(or (identifier? unit1) (identifier? unit2))
            (values scale1
                    scale2
                    (cons (list unit1 expt1 unit2 expt2) conversions)
                    (type-map-set result-units unit2 measure-expt))]
           [else
            (match (reconcile-units unit1 unit2)
              [#f
               (type-error #:src src-stx
                           #:msg "unable to find common unit for ~a and ~a" (resugar* unit1) (resugar* unit2))]
              [(list s1 s2 common-unit)
               #;(printf "found scale factors ~a and ~a, expt=~a\n" s1 s2 expt1)
               (values (* scale1 (expt s1 expt1))
                       (* scale2 (expt s2 expt2))
                       conversions
                       (type-map-set result-units common-unit measure-expt))])])
         ]
        [(#f (cons unit2 _expt2))
         (values scale1
                 scale2
                 conversions
                 (type-map-set result-units unit2 measure-expt))]
        [((cons unit1 _expt1) #f)
         (values scale1
                 scale2
                 conversions
                 (type-map-set result-units unit1 measure-expt))]
        [(#f #f)
         (error 'bridge-units-of-common-measure
                "error looking up units for measure ~a" (resugar* measure))])))

  (define (normalize&combine t1 t2 #:expt-scaler [expt-scaler 1])
    (define t1+ (normalize t1))
    (define t2+ (normalize t2))
    #;(printf "t1+: ~a\n" (format-normalized t1+))
    (define scaled-t2+ (type-map-map-values (lambda (n) (* expt-scaler n)) t2+))
    #;(printf "scaled-t2+: ~a\n" (format-normalized scaled-t2+))
    (define combined (type-map-combine t1+ scaled-t2+ +))
    #;(printf "combined: ~a\n" (format-normalized combined))
    (define denormalized (denormalize combined))
    #;(printf "denormalized: ~a\n" denormalized)
    (values t1+
            scaled-t2+
            combined
            denormalized))

  (define (constraint-effs conversion-constraints)
    (for/list ([c (in-list conversion-constraints)])
      (match-define (list u1 _e1 u2 _e2) c)
      #`(<~> #,u1 #,u2)))

  (define (scale-with-conversions stx scale conversions ctx)
    (printf "scaling with conversions ~a\n" conversions)
    (define conversion-exprs
      (for/list ([c (in-list conversions)])
        (match-define (list u1 e1 u2 _e2) c)
        (printf "conversions REF\nbinding:~a\n~a\n"
                (identifier-binding (datum->syntax ctx 'conversions))
                (syntax-debug-info (datum->syntax ctx 'conversions) #;(current-conversion-dict) (syntax-local-phase-level) #t)
                #;(syntax-debug-info (syntax-local-introduce (current-conversion-dict))))
        (quasisyntax/loc stx
          (*- (expt- (hash-ref- #,(datum->syntax ctx 'conversions) #;#,(syntax-local-introduce (current-conversion-dict))
                                '#,(conversion-name u1 u2))
                     '#,e1)))))
    (cond
      [(and (empty? conversion-exprs)
            (= 1 scale))
       stx]
      [(= 1 scale)
       (quasisyntax/loc stx
         (*- #,@conversion-exprs #,stx))]
      [(empty? conversion-exprs)
       (quasisyntax/loc stx
         (*- '#,scale #,stx))]
      [else
       (quasisyntax/loc stx
         (*- '#,scale #,@conversion-exprs #,stx))]))

  (define (conversion-name unit-from unit-to)
    (define (fmt t) (syntax->datum (resugar* t)))
    (format-id unit-from "~a->~a" (fmt unit-from) (fmt unit-to)))
  )





(define-typed-syntax *
  [(_ e1 e2)
   ≫
   ;; e.g. (* Distance Distance)
   [⊢ e1 ≫ e1- ⇒ ~Measure]
   [⊢ e2 ≫ e2- ⇒ ~Measure]
   #:do [(define-values (_ denormalized) (normalize&combine #'e1- #'e2- #:expt-scaler -1))]
   --------------------
   [⊢ #,denormalized ⇒ Measure]]
  [(_ e1 e2)
   ≫
   [⊢ e1 ≫ u1- ⇒ m1]
   [⊢ e2 ≫ u2- ⇒ m2]
   [⊢ m1 ≫ m1- ⇐ Measure]
   [⊢ m2 ≫ m2- ⇐ Measure]
   #:do [
         (define-values (_a _b normalized-measures denormalized-measures)
           (normalize&combine #'m1- #'m2-))
         (define-values (u1+ neg-u2+ _normalized-units _denormalized-units)
           (normalize&combine #'u1- #'u2-))
         (define-values (_s1 _s2  _constraints combined-units)
           (bridge-units-of-common-measure normalized-measures u1+ neg-u2+ #:src this-syntax))
         (define res-units (denormalize combined-units))
         #;(printf "combined measures: ~a\n" (format-normalized normalized-measures))
         #;(printf "combined units: ~a\n" (format-normalized combined-units))
         #;(printf "res-measure: ~a\n" (syntax->datum denormalized-measures))
         #;(printf "res-units: ~a\n" (syntax->datum res-units))
         ]
   --------------------
   [⊢ #,res-units ⇒ #,denormalized-measures]]
  [(_ e1 e2)
   ≫
   ;; e.g. (* 3m 5s)
   [⊢ e1 ≫ e1- (⇒ : (~Num u1)) (⇒ ν (~effs cc1 ...))]
   [⊢ e2 ≫ e2- (⇒ : (~Num u2)) (⇒ ν (~effs cc2 ...))]
   [⊢ u1 ≫ u1- ⇒ m1]
   [⊢ u2 ≫ u2- ⇒ m2]
   [⊢ m1 ≫ m1- ⇐ Measure]
   [⊢ m2 ≫ m2- ⇐ Measure]
   #:do [
         (define-values (_a _b normalized-measures denormalized-measures)
           (normalize&combine #'m1- #'m2-))
         #;(printf "combined measures: ~a\n" (format-normalized normalized-measures))
         (define-values (u1+ neg-u2+ _normalized-units _denormalized-units)
           (normalize&combine #'u1- #'u2-))
         (define-values (scale1 scale2 constraints combined-units)
           (bridge-units-of-common-measure normalized-measures u1+ neg-u2+ #:src this-syntax))
         #;(printf "combined units: ~a\n" (format-normalized combined-units))
         (define res-units (denormalize combined-units))
         #;(printf "res-measure: ~a\n" (syntax->datum denormalized-measures))
         #;(printf "res-units: ~a\n" (syntax->datum res-units))
         ]
   --------------------
   [⊢ (*- #,(scale-with-conversions #'e1- scale1 constraints this-syntax)
          #,(scale-with-conversions #'e2- scale2 '() this-syntax))
      (⇒ : (Num #,res-units))
      (⇒ ν (cc1 ... cc2 ... #,@(constraint-effs constraints)))]])

(define-typed-syntax /
  [(_ 1 e)
   ≫
   ;; e.g. (/ 1 Time)
   [⊢ e ≫ e- ⇒ ~Measure]
   --------------------
   [≻ (Div 1 e-)]]
  [(_ 1 e)
   ≫
   ;; e.g. (/ 1 Seconds)
   [⊢ e ≫ e- ⇒ t]
   [⊢ t ≫ _ ⇐ Measure]
   --------------------
   [≻ (Div 1 e-)]]
  [(_ e1 e2)
   ≫
   ;; e.g. (/ Distance Time)
   [⊢ e1 ≫ e1- ⇒ ~Measure]
   [⊢ e2 ≫ e2- ⇒ ~Measure]
   #:do [(define-values (_ denormalized) (normalize&combine #'e1- #'e2- #:expt-scaler -1))]
   --------------------
   [⊢ #,denormalized ⇒ Measure]]
  [(_ e1 e2)
   ≫
   ;; e.g. (/ Meters Second)
   [⊢ e1 ≫ u1- ⇒ m1]
   [⊢ e2 ≫ u2- ⇒ m2]
   [⊢ m1 ≫ m1- ⇐ Measure]
   [⊢ m2 ≫ m2- ⇐ Measure]
   #:do [
         (define-values (_a _b normalized-measures denormalized-measures)
           (normalize&combine #'m1- #'m2- #:expt-scaler -1))
         (define-values (u1+ neg-u2+ _normalized-units _denormalized-units)
           (normalize&combine #'u1- #'u2- #:expt-scaler -1))
         (define-values (_s1 _s2 _constraints combined-units)
           (bridge-units-of-common-measure normalized-measures u1+ neg-u2+ #:src this-syntax))
         (define res-units (denormalize combined-units))
         #;(printf "combined measures: ~a\n" (format-normalized normalized-measures))
         #;(printf "combined units: ~a\n" (format-normalized combined-units))
         #;(printf "res-measure: ~a\n" (syntax->datum denormalized-measures))
         #;(printf "res-units: ~a\n" (syntax->datum res-units))
         ]
   --------------------
   [⊢ #,res-units ⇒ #,denormalized-measures]]
  [(_ e1 e2)
   ≫
   ;; e.g. (/ 3m 5s)
   [⊢ e1 ≫ e1- (⇒ : (~Num u1)) (⇒ ν (~effs cc1 ...))]
   [⊢ e2 ≫ e2- (⇒ : (~Num u2)) (⇒ ν (~effs cc2 ...))]
   [⊢ u1 ≫ u1- ⇒ m1]
   [⊢ u2 ≫ u2- ⇒ m2]
   [⊢ m1 ≫ m1- ⇐ Measure]
   [⊢ m2 ≫ m2- ⇐ Measure]
   #:do [
         (define-values (_a _b normalized-measures denormalized-measures)
           (normalize&combine #'m1- #'m2- #:expt-scaler -1))
         (define-values (u1+ neg-u2+ _normalized-units _denormalized-units)
           (normalize&combine #'u1- #'u2- #:expt-scaler -1))
         (define-values (scale1 scale2 constraints combined-units)
           (bridge-units-of-common-measure normalized-measures u1+ neg-u2+ #:src this-syntax))
         (define res-units (denormalize combined-units))
         #;(printf "combined measures: ~a\n" (format-normalized normalized-measures))
         #;(printf "combined units: ~a\n" (format-normalized combined-units))
         #;(printf "res-measure: ~a\n" (syntax->datum denormalized-measures))
         #;(printf "res-units: ~a\n" (syntax->datum res-units))
         ]
   --------------------
   [⊢ (/- #,(scale-with-conversions #'e1- scale1 constraints this-syntax)
          #,(scale-with-conversions #'e2- scale2 '() this-syntax))
      (⇒ : (Num #,res-units))
      (⇒ ν (cc1 ... cc2 ... #,@(constraint-effs constraints)))]
   ])

(define-typed-syntax (+ e1 e2) ≫
  #:do [(printf "expanding +\n")
        (printf "conversions binding: ~a\n" (identifier-binding (datum->syntax this-syntax 'conversions)))
        #;(printf "bound symbols:\n~a\n" (syntax-bound-symbols this-syntax))]
  [⊢ e1 ≫ e1- (⇒ : (~Num u1)) (⇒ ν (~effs cc1 ...))]
  [⊢ e2 ≫ e2- (⇒ : (~Num u2)) (⇒ ν (~effs cc2 ...))]
  #:do [(displayln '+A)]
  [⊢ u1 ≫ _ ⇒ m1]
  [⊢ u2 ≫ _ ⇒ m2]
  #:do [(displayln '+B)]
  [⊢ m1 ≫ _ ⇐ Measure]
  [⊢ m2 ≫ _ ⇐ Measure]
  #:do [(displayln '+C)]
  #:do [
        (define m1+ (normalize #'m1))
        (define m2+ (normalize #'m2))
        ]
  #:fail-unless (type-map-equal/in-order? m1+ m2+) (format "Can only add equivalent measures; got ~a and ~a"
                                                           (format-normalized m1+)
                                                           (format-normalized m2+))
  #:do [
        (define u1+ (normalize #'u1))
        (define u2+ (normalize #'u2))
        (define-values (scale1 scale2 constraints res-tys)
          (bridge-units-of-common-measure m1+ u1+ u2+ #:src this-syntax))
        ]
  #:do [(displayln '+D)]
  #:with u (denormalize res-tys)
  --------------------
  [⊢ (+- #,(scale-with-conversions #'e1- scale1 constraints this-syntax)
         #,(scale-with-conversions #'e2- scale2 '() this-syntax))
     (⇒ : (Num u))
     (⇒ ν (cc1 ... cc2 ... #,@(constraint-effs constraints)))])


(define-typed-syntax (:: n:number U) ≫
  [⊢ U ≫ U- ⇒ M]
  #:fail-unless ((current-typecheck-relation) #'U- ((current-type-eval) #'Unit))
                (format ":: expected Unit, got ~a" #'U-)
  [⊢ M ≫ _ ⇐ Measure]
  --------------------
  [⊢ n
     (⇒ : (Num U-))])


(define-typed-syntax (print e:expr) ≫
  [⊢ e ≫ e- ⇒ (~or* (~Num ty) ty)]
  [⊢ ty ≫ ty- ⇒ K]
  #:with ty+ (resugar-type #'ty)
  #:with norm (syntax-parse #'K
                [~Measure
                 (format-normalized (normalize #'ty))]
                [_
                 ""])
  --------------------
  [≻ (printf- "~a :: ~a ~~ ~a\n"
              e-
              (syntax->datum #'ty+)
              'norm)])


(define-typed-syntax define
  [(_ x:id e:expr)
   ≫
   --------------------
   [≻ (define-typed-variable x e)]]
  [(_ (fun:id [TyArg:id (~datum ::) Unit] ...
              [TermArg:id (~datum :) Ty] ...)
      body)
   ≫
   [⊢ (define/fun/cont
        ([TyArg Unit] ...)
        (TyArg ...)
        ([TermArg Ty] ...)
        fun
        body)
      ≫ lam-
      ⇒ fun-ty]
   #:with fun- (generate-temporary #'fun)
   --------------------
   [≻ (begin-
        (define- fun- lam-)
        (define-typed-variable-rename fun ≫ fun- : fun-ty))]
   ])

(define-typed-syntax define/fun/cont
  [(_ ([TyArg Unit] TyArgs ...)
      TyVars
      TermArgs
      fun
      body)
   ≫
   #:cut
   [⊢ Unit ≫ Unit- ⇒ M]
   [⊢ M ≫ M- ⇐ Measure]
   [[TyArg ≫ _ : Unit-]
    ⊢
    (define/fun/cont (TyArgs ...) TyVars TermArgs fun body)
    ≫
    body-
    ]
   --------------------
   [≻ body-]]
  [(_ ()
      (TyArg ...)
      ([TermArg Ty] ...)
      fun
      body)
   ≫
   #:cut
   [⊢ (lambda ([TermArg : Ty] ...) body) ≫ lam- ⇒ lam-ty]
   #:do [(printf "\nRECEIVED expanded lambda!\n")]
   ;; [[TermArg ≫ TermArg- : Ty]
   ;;  ...
   ;;  ⊢
   ;;  body ≫ body-
   ;;  (⇒ : body-ty)
   ;;  (⇒ ν (~effs cc ...))]
   [⊢ TyArg ≫ TyArg- ⇒ K] ...
   ;; #:with lam-ty #'(→ (ConversionConstraints cc ...)
   ;;                    body-ty
   ;;                    Ty ...)
   #:with Lam-ty #'(Λ+ ([TyArg- K] ...) lam-ty)
   --------------------
   [⊢ lam- ⇒ Lam-ty]])

(define-for-syntax (unpack-conversions dict-id conversions body-stx)
  (syntax-parse conversions
    [()
     body-stx]
    [((~<~> u1 u2) ...)
     #:with (nm ...) (stx-map conversion-name #'(u1 ...) #'(u2 ...))
     (quasisyntax/loc body-stx
       (let– ([nm (hash-ref- #,dict-id 'nm)]
              ...)
         #,body-stx))])
  )

(define-typed-syntax (lambda ([x:id (~datum :) ty] ...) body) ≫
  #:do [(printf "expanding lambda\n")]
  #:with conversion-dict (format-id #'body "conversions")
   ;; #:do [(printf "conversions bind\n~a\n~a\n"
   ;;               (syntax-debug-info (current-conversion-dict))
   ;;               (syntax-debug-info (syntax-local-introduce (current-conversion-dict))))
   ;;       ]
   [[x ≫ x- : ty]
    ...
    [conversion-dict ≫ conversion-dict- : Type]
    ⊢ body ≫ body-
    (⇒ : body-ty)
    (⇒ ν (~effs cc ...))]
  #:do [(printf "\nEXPANDED LAMBDA!\n")]
  --------------------
  [⊢ (lambda- (conversion-dict- x- ...) body-
              #;#,(unpack-conversions #'conversion-dict #'(cc ...) #'body-))
     ⇒ (→ (ConversionConstraints cc ...)
          body-ty
          ty ...)])
