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
         lambda
         define
         (rename-out [typed-apply #%app])
         (for-syntax conversions))

(require (for-syntax "type-map.rkt")
         turnstile/typedefs
         (only-in racket/hash hash-union))

;; Runtime helper for merging conversion dictionaries
(define hash-union- hash-union)

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
    (let loop ([bvs/rev '()]
               [stx stx])
      (syntax-parse stx
        [(~Λ [bv : k] body)
         (loop (cons #'(bv : k) bvs/rev)
               #'body)]
        [_
         #`(#,(reverse bvs/rev) #,stx)])))

  (define-syntax ~Λ+
    (pattern-expander
     (syntax-parser
       [(_ tvs-pat body-pat)
        #'(~or* (~and lam
                      (~Λ [_ : _] _)
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
    (define conversion-exprs
      (for/list ([c (in-list conversions)])
        (match-define (list u1 e1 u2 _e2) c)
        (quasisyntax/loc stx
          (*- (expt- (hash-ref- #,(gen-conversions-id ctx)
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

  (define (type-var-id? id)
    (syntax-property id 'type-variable))

  ;; Extract the original identifier from a type that may have been substituted
  ;; Uses the 'orig syntax property to find the original variable name
  ;; Looks for identifiers marked with 'type-variable property
  (define (get-original-identifier ty)
    (define orig-prop (syntax-property ty 'orig))
    (cond
      ;; If orig property exists and contains the substitution history
      [(and orig-prop (pair? orig-prop))
       ;; Search for an identifier marked as a type variable
       (let loop ([prop orig-prop])
         (cond
           [(and (identifier? prop) (type-var-id? prop))
            prop]
           [(pair? prop)
            (or (loop (car prop)) (loop (cdr prop)))]
           [else #f]))]
      ;; If no orig property, check if ty itself is a type variable
      [(and (identifier? ty) (type-var-id? ty))
       ty]
      ;; Otherwise return as-is
      [(identifier? ty) ty]
      [else #f]))

  (define (conversion-name unit-from unit-to)
    ;; Try to get original identifiers for stable naming across substitution
    (define orig-from (or (get-original-identifier unit-from) unit-from))
    (define orig-to (or (get-original-identifier unit-to) unit-to))
    (define (fmt t) (syntax->datum (resugar* t)))
    (format-id unit-from "~a->~a" (fmt orig-from) (fmt orig-to)))

  ;; Constants for conversion dictionary names
  (define CONVERSIONS-NAME 'conversions)
  (define CONVERSIONS-INNER-NAME 'conversions/inner)

  ;; Generate identifier for the merged conversion dictionary
  (define (gen-conversions-id ctx)
    (datum->syntax ctx CONVERSIONS-NAME))

  ;; Generate identifier for this lambda's conversion parameter
  (define (gen-conversions-inner-id ctx)
    (datum->syntax ctx CONVERSIONS-INNER-NAME))

  ;; Check if a constraint mentions any of the given type variables
  ;; Assumes constraint is already expanded/normalized
  (define (constraint-mentions-tvars? constraint tvars)
    (syntax-parse constraint
      [(~<~> u1 u2)
       (define vars (append (collect-free-ids #'u1) (collect-free-ids #'u2)))
       (for/or ([v (in-list vars)])
         (for/or ([tv (in-list (syntax->list tvars))])
           (free-identifier=? v tv)))]
      [other #f]))

  ;; Collect free identifiers in a type
  (define (collect-free-ids ty)
    (let loop ([ty ty]
               [acc '()])
      (syntax-parse ty
        [(~ProdInt t1 t2)
         (loop #'t2 (loop #'t1 acc))]
        [(~DivInt t1 t2)
         (loop #'t2 (loop #'t1 acc))]
        [(~Num u)
         (loop #'u acc)]
        [~Dimensionless acc]
        [x:id
         (cons #'x acc)]
        [_ acc])))

  ;; Partition constraints based on whether they mention local type variables
  (define (partition-constraints constraints local-tvars)
    ;; First, expand all constraints to their normalized forms
    (define constraints-expanded
      (for/list ([c (in-list (syntax->list constraints))])
        ((current-type-eval) c)))
    (for/fold ([local '()]
               [outer '()]
               #:result (values (reverse local) (reverse outer)))
              ([c (in-list constraints-expanded)])
      (define mentions? (constraint-mentions-tvars? c local-tvars))
      (if mentions?
          (values (cons c local) outer)
          (values local (cons c outer)))))
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
   ;; [⊢ e1 ≫ e1- (⇒ : t) (⇒ ν (~effs cc1 ...))]
   ;; #:do [(printf "e1 : ~a\n" #'t)]
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
  [⊢ e1 ≫ e1- (⇒ : (~Num u1)) (⇒ ν (~effs cc1 ...))]
  [⊢ e2 ≫ e2- (⇒ : (~Num u2)) (⇒ ν (~effs cc2 ...))]
  [⊢ u1 ≫ _ ⇒ m1]
  [⊢ u2 ≫ _ ⇒ m2]
  [⊢ m1 ≫ _ ⇐ Measure]
  [⊢ m2 ≫ _ ⇐ Measure]
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
   --------------------
   [≻ (define fun (lambda ([TyArg :: Unit] ... [TermArg : Ty] ...) body))]
   ])

(define-typed-syntax define/fun/cont
  [(_ ([TyArg Unit] TyArgs ...)
      TyVars
      TermArgs
      body)
   ≫
   #:cut
   [⊢ Unit ≫ Unit- ⇒ M]
   [⊢ M ≫ M- ⇐ Measure]
   [[TyArg ≫ _ : Unit-]
    ⊢
    (define/fun/cont (TyArgs ...) TyVars TermArgs body)
    ≫
    body-
    ]
   --------------------
   [≻ body-]]
  [(_ ()
      (TyArg ...)
      ([TermArg Ty] ...)
      body)
   ≫
   #:cut
   [⊢ (lambda ([TermArg : Ty] ...) body) ≫ lam- ⇒ lam-ty]
   #:do [(printf "\nRECEIVED expanded lambda!\n")]
   [⊢ TyArg ≫ TyArg- ⇒ K] ...
   #:with Lam-ty #'(Λ+ ([TyArg- K] ...) lam-ty)
   --------------------
   [⊢ lam- ⇒ Lam-ty]])

(define-typed-syntax (lambda ([X:id (~datum ::) K] ... [x:id (~datum :) ty] ...) body) ≫
  --------------------
  [≻ (lambda-telescope ([X K] ...)
                       (X ...)
                       ([x ty] ...)
                       body)])

(define-typed-syntax lambda-telescope
  [(_ ([TyArg Unit] TyArgs ...)
      TyVars
      TermArgs
      body)
   ≫
   #:cut
   [⊢ Unit ≫ Unit- ⇒ M]
   [⊢ M ≫ M- ⇐ Measure]
   #:with TyArg-marked (attach #'TyArg 'type-variable #t)
   [[TyArg-marked ≫ _ : Unit-]
    ⊢
    #,(subst #'TyArg-marked #'TyArg #'(lambda-telescope (TyArgs ...) TyVars TermArgs body))
    ≫
    body-
    ]
   --------------------
   [≻ body-]]
  [(_ ()
      (TyArg ...)
      ([x ty] ...)
      body)
   ≫
   #:cut
   #:with conversions-merged (gen-conversions-id #'body)
   #:with conversion-dict-inner (gen-conversions-inner-id #'body)
   #:do [(define has-outer? (identifier-binding #'conversions-merged))]
   [⊢ ty ≫ ty- ⇒ _] ...
   [[x ≫ x- : ty-]
    ...
    [conversion-dict-inner ≫ conversion-dict-inner- : Type]
    [conversions-merged ≫ conversions-merged- : Type]
    ⊢ body ≫ body-
    (⇒ : body-ty)
    (⇒ ν (~effs cc ...))]
   [⊢ TyArg ≫ TyArg- ⇒ K] ...
   #:do [
         ;; Partition constraints: local vs outer
         (define-values (local-cc outer-cc)
           (partition-constraints #'(cc ...) #'(TyArg- ...)))
         ]
   #:with (local-cc* ...) local-cc
   #:with (outer-cc* ...) outer-cc
   #:with lam-ty #'(→ (ConversionConstraints local-cc* ...)
                      body-ty
                      ty- ...)
   #:with Lam-ty #'(Λ+ ([TyArg- K] ...) lam-ty)
   --------------------
   [⊢ (lambda- (conversion-dict-inner- x- ...)
        (let- ([conversions-merged- #,(if has-outer?
                                          #'(hash-union- conversions-merged conversion-dict-inner-)
                                          #'conversion-dict-inner-)])
          body-))
      (⇒ : Lam-ty)
      (⇒ ν (outer-cc* ...))]])

(define-typed-syntax (typed-apply fn-exp arg-exp ...) ≫
  [⊢ fn-exp ≫ fn-exp- ⇒ fn-ty]
  #:with (~Λ+ ([U : M] ...) (~→ (~ConversionConstraints (~<~> u1 u2) ...)
                                ty-ret
                                ty-arg ...)) #'fn-ty
  #:fail-unless (stx-length>=? #'(ty-arg ...) #'(arg-exp ...))
  (format "Required ~a arguments, received ~a" (stx-length #'(ty-arg ...)) (stx-length #'(arg-exp ...)))
  [⊢ arg-exp ≫ arg-exp- ⇒ arg-ty] ...
  #:do [
        (define-values (subst-xs subst-tys unsolved)
          (unify #'([U M] ...) #'([ty-arg arg-ty] ...) this-syntax))
        ]
  #:fail-unless (empty? unsolved) (format "Failed to solve for variables: ~a" unsolved)
  #:with (ty-ret- (u1- u2-) ...) (substs subst-tys subst-xs #'(ty-ret (u1 u2) ...))
  #:with dict-expr (build-conversion-dict-expr #'([u1 u1- u2 u2-] ...) this-syntax)
  --------------------
  [⊢ (#%app- fn-exp- dict-expr arg-exp- ...) ⇒ ty-ret-])

(define-for-syntax (build-conversion-dict-expr ts ctx)
  (syntax-parse ts
    [([u1 u1- u2 u2-] ...)
     #:with (key-nm ...) (stx-map conversion-name #'(u1 ...) #'(u2 ...))
     #:with (scale ...) (for/list ([u (in-syntax #'(u1- ...))]
                                   [v (in-syntax #'(u2- ...))])
                          (match (reconcile-units u v)
                            [#f
                             (type-error #:src ctx
                                         #:msg "unable to find common unit for ~a and ~a" (resugar* u) (resugar* v))]
                            [(list s1 _s2 _common-unit)
                             s1]))
    #'(hash- (~@ 'key-nm 'scale) ...)]))

(define-for-syntax (unify tvs0 constraints0 ctx)
  (syntax-parse #`(#,tvs0 #,constraints0)
    [(([U M] ...) ([ty-arg arg-ty] ...))
     (define kind-constraints (for/fold ([tm (make-type-map)])
                                        ([u (in-syntax #'(U ...))]
                                         [m (in-syntax #'(M ...))])
                                (type-map-set tm u m)))
     (define eq-constraints (for/list ([t1 (in-syntax #'(ty-arg ...))]
                                       [t2 (in-syntax #'(arg-ty ...))])
                                 (list t1 t2)))
     (define =? (current-typecheck-relation))
     (let loop ([tvs kind-constraints]
                [constraints eq-constraints]
                [subst-xs '()]
                [subst-tys '()])
       (match constraints
         ['()
          (define unsolved (for/fold ([tvs tvs]
                                      #:result (type-map-keys tvs))
                                     ([x (in-list subst-xs)])
                             (type-map-remove tvs x)))
          (values subst-xs subst-tys unsolved)]
         [(cons (list t1 t2) constraints*)
          (syntax-parse (substs subst-tys subst-xs #`(#,t1 #,t2))
            [(a b)
             #:when (=? #'a #'b)
             (loop tvs constraints* subst-xs subst-tys)]
            [(X:id ty)
             (when (stx-contains-id? #'ty #'X)
               (type-error #:src ctx
                           #:msg "Encountered recursive type constraint with ~a and ~a"
                           (syntax->datum #'X)
                           (resugar* #'ty)))
             (define kind (type-map-ref tvs #'X))
             (loop tvs
                   (cons (list kind (typeof #'ty)) constraints)
                   (cons #'X subst-xs)
                   (cons #'ty subst-tys))
             ]
            [((~Num a) (~Num b))
             (loop tvs (cons (list #'a #'b) constraints*) subst-xs subst-tys)]
            [((~ProdInt a1 a2) (~ProdInt b1 b2))
             (loop tvs (cons (list #'a1 #'b1) (cons (list #'a2 #'b2) constraints*)) subst-xs subst-tys)]
            [((~DivInt a1 a2) (~DivInt b1 b2))
             (loop tvs (cons (list #'a1 #'b1) (cons (list #'a2 #'b2) constraints*)) subst-xs subst-tys)]
            [(a b)
             (type-error #:src ctx
                         #:msg "Failure during unification between ~a and ~a"
                         #'a
                         #'b)])
          ]))
     ])
  )
