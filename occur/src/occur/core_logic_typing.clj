(ns occur.core-logic-typing
  (:require [clojure.set :as set])
  (:refer-clojure :exclude [type]))

;;; ---- Type System Core ----

;; Basic primitive types
(def int-type :int)
(def string-type :string)
(def bool-type :bool)
(def any-type :any)
(def bottom-type :bottom)

;; Forward declarations to avoid circular dependencies
(declare typecheck apply-formula extract-formula extract-param-predicates substitute-var intersect-types function-type)

;; ----- #10: Add a Type Class Hierarchy -----
;; Define a protocol for type operations to create a more extensible system
(defprotocol TypeOps
  "Protocol for operations on types"
  (is-subtype? [this other] "Is this a subtype of other?")
  (intersect [this other] "Intersection of two types")
  (subtract [this other] "Subtract other from this type"))

;; Extend the protocol to primitive type keywords
(extend-protocol TypeOps
  clojure.lang.Keyword
  (is-subtype? [this other]
    (cond
      ;; Any primitive type is a subtype of itself
      (= this other) true
      ;; Any type is a subtype of :any
      (= other any-type) true
      ;; If other is a union, check if this is a subtype of any type in the union
      (set? other) (contains? other this)
      ;; Otherwise not a subtype
      :else false))

  (intersect [this other]
    (cond
      ;; Intersection with itself returns itself
      (= this other) this
      ;; Intersection with any returns this
      (= other any-type) this
      ;; Intersection with a union
      (set? other) (if (contains? other this) this bottom-type)
      ;; Different primitive types have empty intersection
      :else bottom-type))

  (subtract [this other]
    (cond
      ;; Subtracting itself gives bottom
      (= this other) bottom-type
      ;; Subtracting a union that contains this type returns bottom
      (and (set? other) (contains? other this)) bottom-type
      ;; Otherwise, the type is unchanged
      :else this)))

;; Extend the protocol to sets (union types)
(extend-protocol TypeOps
  clojure.lang.IPersistentSet
  (is-subtype? [this other]
    (cond
      ;; Empty set is a subtype of anything
      (empty? this) true
      ;; Any set is a subtype of :any
      (= other any-type) true
      ;; If other is a set, check if every element in this is a subtype of some element in other
      (set? other) (every? #(contains? other %) this)
      ;; If other is a primitive, this can't be a subtype unless it's a singleton
      (and (= (count this) 1) (is-subtype? (first this) other)) true
      ;; Otherwise not a subtype
      :else false))

  (intersect [this other]
    (cond
      ;; Intersection with any returns this
      (= other any-type) this
      ;; If other is a primitive type, check if it's in this
      (keyword? other) (if (contains? this other) other bottom-type)
      ;; If other is a set, take the intersection of the sets
      (set? other) (let [result (set/intersection this other)]
                     (if (empty? result)
                       bottom-type
                       (if (= (count result) 1)
                         (first result)
                         result)))
      ;; Default case
      :else bottom-type))

  (subtract [this other]
    (cond
      ;; Subtracting :any gives bottom
      (= other any-type) bottom-type
      ;; Subtracting a primitive type
      (keyword? other) (let [result (disj this other)]
                         (if (empty? result)
                           bottom-type
                           (if (= (count result) 1)
                             (first result)
                             result)))
      ;; Subtracting a set
      (set? other) (let [result (set/difference this other)]
                     (if (empty? result)
                       bottom-type
                       (if (= (count result) 1)
                         (first result)
                         result)))
      ;; Default case
      :else this)))

;; Extend the protocol to maps (function types)
(extend-protocol TypeOps
  clojure.lang.IPersistentMap
  (is-subtype? [this other]
    (cond
      ;; Any function type is a subtype of :any
      (= other any-type) true
      
      ;; If other is also a function type, check for function subtyping
      (and (map? other) 
           (= (:type this) :function)
           (= (:type other) :function))
      (let [this-params (:param-types this)
            other-params (:param-types other)
            this-return (:return-type this)
            other-return (:return-type other)]
        ;; For a function to be a subtype:
        ;; 1. It must accept at least the same parameter types (contravariant)
        ;; 2. It must return a subtype of the other function's return type (covariant)
        ;; 3. Same number of parameters
        (and (= (count this-params) (count other-params))
             (every? identity (map #(is-subtype? %2 %1) this-params other-params))
             (is-subtype? this-return other-return)))
      
      ;; Not a subtype in other cases
      :else false))
  
  (intersect [this other]
    (cond
      ;; Intersection with any returns this
      (= other any-type) this
      
      ;; Intersection with the same function type
      (= this other) this
      
      ;; Intersection with a compatible function type
      (and (map? other) 
           (= (:type this) :function)
           (= (:type other) :function))
      (let [this-params (:param-types this)
            other-params (:param-types other)
            this-return (:return-type this)
            other-return (:return-type other)]
        ;; If parameters have the same count, try to find intersection
        (if (= (count this-params) (count other-params))
          (let [param-intersections (mapv #(intersect-types %1 %2) 
                                        this-params other-params)
                return-intersection (intersect-types this-return other-return)]
            ;; If any parameter intersection is bottom, the whole intersection is bottom
            (if (or (some #(= % bottom-type) param-intersections)
                    (= return-intersection bottom-type))
              bottom-type
              ;; Otherwise create a new function type with the intersections
              (function-type param-intersections 
                           return-intersection)))
          ;; Different parameter counts - no intersection
          bottom-type))
      
      ;; Default case - no intersection
      :else bottom-type))
  
  (subtract [this other]
    (cond
      ;; Subtracting :any gives bottom
      (= other any-type) bottom-type
      
      ;; Subtracting the same function type
      (= this other) bottom-type
      
      ;; Default case - no good way to subtract function types partially
      :else this)))

;; Wrapper functions that use the protocol
(defn subtype? [sub-type super-type]
  (is-subtype? sub-type super-type))

(defn intersect-types [t1 t2]
  (intersect t1 t2))

(defn type-difference [t1 t2]
  (subtract t1 t2))

;; Remaining type constructors and utility functions with minor adjustments
(defn union-type
  "Create a union type from a collection of types.
   Can be called with either a collection or multiple arguments."
  [types & more-types]
  (let [all-types (if (and (coll? types) (empty? more-types))
                   types
                   (cons types more-types))
        flattened (set (mapcat #(if (set? %) % [%]) all-types))]
    (cond
      (empty? flattened) bottom-type
      (= 1 (count flattened)) (first flattened)
      :else flattened)))

(defn function-type
  "Create a function type with given param-types, return-type and optional latent predicates.
   Latent predicates are formulas that are proven about parameters and return value."
  [param-types return-type & {:keys [latent-predicates]}]
  {:type :function
   :param-types param-types
   :return-type return-type
   :latent-predicates (or latent-predicates {})})

;; Type predicates for the unified type representation
(defn primitive-type? [t] (keyword? t))
(defn union-type? [t] (set? t))
(defn function-type? [t] (and (map? t) (= (:type t) :function)))

;; Helper to consistently get types from a union
(defn union-types [t]
  (if (set? t) t #{t}))

;; Check if a type can be used in boolean context
(defn compatible-with-bool? [t]
  (cond
    (= t bool-type) true
    (and (set? t) (contains? t bool-type)) true
    :else false))

;;; ---- Constraint System ----

;; ----- #7: Decouple Boolean Logic Processing -----
;; Create a clear separation between boolean logic and type checking

;; Boolean Constraint Types
(defn type-constraint [var type]
  {:constraint :type, :var var, :type type})

;; Boolean Operators
(defn conjunction
  "Create a conjunction (logical AND) of clauses.
   Handles special cases like empty conjunctions and singleton conjunctions."
  [clauses]
  (cond
    ;; Empty conjunction is true
    (empty? clauses) true
    ;; Single clause conjunction is just the clause
    (= (count clauses) 1) (first clauses)
    ;; Handle boolean constants
    (some false? clauses) false
    (= (set clauses) #{true}) true
    ;; Remove true values and handle one remaining
    :else (let [filtered (filter #(not= % true) clauses)]
            (if (= (count filtered) 1)
              (first filtered)
              {:constraint :conjunction, :clauses filtered}))))

(defn disjunction
  "Create a disjunction (logical OR) of clauses.
   Handles special cases like empty disjunctions and singleton disjunctions."
  [clauses]
  (cond
    ;; Empty disjunction is false
    (empty? clauses) false
    ;; Single clause disjunction is just the clause
    (= (count clauses) 1) (first clauses)
    ;; Handle boolean constants
    (some true? clauses) true
    (= (set clauses) #{false}) false
    ;; Remove false values and handle one remaining
    :else (let [filtered (filter #(not= % false) clauses)]
            (if (= (count filtered) 1)
              (first filtered)
              {:constraint :disjunction, :clauses filtered}))))

(defn negation
  "Create a negation (logical NOT) of a formula.
   Handles double negation and constants."
  [formula]
  (cond
    ;; Negating constants
    (= formula true) false
    (= formula false) true
    ;; Negating a negation (double negation elimination)
    (and (map? formula) (= (:constraint formula) :negation))
    (:formula formula)
    ;; Standard negation
    :else {:constraint :negation, :formula formula}))

;; Boolean Constraint Predicates
(defn type-constraint? [formula]
  (= (:constraint formula) :type))

(defn conjunction? [formula]
  (= (:constraint formula) :conjunction))

(defn disjunction? [formula]
  (= (:constraint formula) :disjunction))

(defn negation? [formula]
  (= (:constraint formula) :negation))

;; Boolean Formula Normalization
(defn to-nnf
  "Convert a formula to Negation Normal Form (NNF).
   In NNF, negations only appear directly in front of atomic formulas."
  [formula]
  (cond
    ;; Constants and atomic constraints remain unchanged
    (or (true? formula) (false? formula) (type-constraint? formula))
    formula

    ;; Process negations according to NNF rules
    (negation? formula)
    (let [inner (:formula formula)]
      (cond
        ;; Negation of constants
        (true?  inner) false
        (false? inner) true
        (type-constraint? inner) formula

        ;; De Morgan's laws: ¬(A ∧ B) ≡ ¬A ∨ ¬B
        (conjunction? inner)
        (to-nnf (disjunction (mapv negation (:clauses inner))))

        ;; De Morgan's laws: ¬(A ∨ B) ≡ ¬A ∧ ¬B
        (disjunction? inner)
        (to-nnf (conjunction (mapv negation (:clauses inner))))

        ;; Double negation elimination: ¬¬A ≡ A
        (negation? inner)
        (to-nnf (:formula inner))))

    ;; Process conjunctions and disjunctions recursively
    (conjunction? formula)
    (let [new-clauses (mapv to-nnf (:clauses formula))]
      (conjunction new-clauses))

    (disjunction? formula)
    (let [new-clauses (mapv to-nnf (:clauses formula))]
      (disjunction new-clauses))

    ;; Default case
    :else formula))

;;; ---- Predicate Handling ----

;; ----- #11: Refactor Predicate Extraction -----
;; Create a declarative registry of predicates for easier maintenance and extension

;; Define a registry of type predicates
(def predicate-registry
  {;; Standard type predicates
   'number? {:type int-type, :extract-fn (fn [expr] (second expr))}
   'string? {:type string-type, :extract-fn (fn [expr] (second expr))}
   'boolean? {:type bool-type, :extract-fn (fn [expr] (second expr))}

   ;; Comparison operators
   '< {:type int-type,
       :extract-fn (fn [expr]
                     (let [vars (filter symbol? (rest expr))]
                       (when (seq vars)
                         (if (= (count vars) 1)
                           (first vars)
                           vars))))}

   '> {:type int-type,
       :extract-fn (fn [expr]
                     (let [vars (filter symbol? (rest expr))]
                       (when (seq vars)
                         (if (= (count vars) 1)
                           (first vars)
                           vars))))}

   ;; Equality operator is special - type depends on the literal
   '= {:type :dynamic,
       :extract-fn (fn [expr]
                     (let [args (rest expr)]
                       (cond
                         ;; var = literal
                         (and (symbol? (first args)) (not (symbol? (second args))))
                         {:var (first args),
                          :literal (second args)}

                         ;; literal = var
                         (and (not (symbol? (first args))) (symbol? (second args)))
                         {:var (second args),
                          :literal (first args)}

                         ;; var = var - handle variable-to-variable equality
                         (and (symbol? (first args)) (symbol? (second args)))
                         {:var1 (first args),
                          :var2 (second args)}

                         ;; other cases not handled
                         :else nil)))}})

;; Helper function to detect primitive type of a literal
(defn literal-type [literal]
  (cond
    (integer? literal) int-type
    (string? literal) string-type
    (boolean? literal) bool-type
    :else nil))

;; Extract a predicate from an expression
(defn extract-predicate
  "Extract type constraints from predicates and comparison expressions.
   Returns a type-constraint or conjunction of constraints, or nil if not applicable."
  [expr]
  (when (and (seq? expr) (not-empty expr))
    (let [op (first expr)]
      (when-let [pred-info (get predicate-registry op)]
        (let [extract-result ((:extract-fn pred-info) expr)]
          (cond
            ;; No variables found
            (nil? extract-result)
            nil

            ;; Single variable for standard predicates
            (and (symbol? extract-result) (not= (:type pred-info) :dynamic))
            (type-constraint extract-result (:type pred-info))

            ;; Multiple variables for comparison operators
            (and (sequential? extract-result) (not= (:type pred-info) :dynamic))
            (conjunction (mapv #(type-constraint % (:type pred-info)) extract-result))

            ;; Special case for equality with literals
            (and (map? extract-result)
                 (= (:type pred-info) :dynamic)
                 (:var extract-result))
            (when-let [var-type (literal-type (:literal extract-result))]
              (type-constraint (:var extract-result) var-type))

            ;; Special case for equality between two variables
            (and (map? extract-result)
                 (= (:type pred-info) :dynamic)
                 (:var1 extract-result)
                 (:var2 extract-result))
            (let [var1 (:var1 extract-result)
                  var2 (:var2 extract-result)]
              ;; Create a constraint that will be handled by apply-constraint
              {:eq-vars [var1 var2]})

            ;; Default case
            :else nil))))))

;; ----- #5: Streamline Extract-Formula -----
;; Break formula extraction into smaller, specialized helper functions

;; Extract formula from a boolean operation (and, or, not)
(defn extract-boolean-op-formula
  "Extract formula from a boolean operation (and, or, not)"
  [op args]
  (case op
    not (when-let [inner (extract-formula (first args))]
          (negation inner))

    and (let [inner-formulas (keep extract-formula args)]
          (when (seq inner-formulas)
            (conjunction inner-formulas)))

    or (let [inner-formulas (keep extract-formula args)]
         (when (seq inner-formulas)
           (disjunction inner-formulas)))

    ;; Not a boolean operation
    nil))

;; Extract formula from an if expression
(defn extract-if-formula
  "Extract formula from an if expression"
  [args]
  (when (seq args)
    (extract-formula (first args))))

;; Extract formula from a non-special form
(defn extract-general-formula
  "Extract formula from a general expression, trying predicates first"
  [expr args]
  (or
   ;; First try to extract a predicate directly
   (extract-predicate expr)

   ;; If not a recognized predicate, try to extract from arguments recursively
   (let [inner-formulas (keep extract-formula args)]
     (when (seq inner-formulas)
       (if (= (count inner-formulas) 1)
         (first inner-formulas)
         (conjunction inner-formulas))))))

;; Main extract-formula function
(defn extract-formula
  "Extract a formula from an expression.
   Handles predicates, boolean operations, and nested expressions."
  [expr]
  (cond
    ;; Literal values - no constraints
    (or (integer? expr) (string? expr) (boolean? expr))
    nil

    ;; Variable reference - no constraints
    (symbol? expr)
    nil

    ;; Sequence expressions
    (seq? expr)
    (let [op (first expr)
          args (rest expr)]
      (or
       ;; Try extracting from boolean operations
       (extract-boolean-op-formula op args)

       ;; Try extracting from if expressions
       (when (= op 'if)
         (extract-if-formula args))

       ;; Try extracting from general expressions
       (extract-general-formula expr args)))

    ;; Default case
    :else nil))

;;; ---- Formula Application Interface ----
;; ----- #8: Eliminate Pattern-Matching Conditionals -----
;; Use a data-driven approach for formula application

;; Refine a variable's type in the environment
(defn refine-env
  "Refine a variable's type in the environment based on a type constraint.
   Returns the updated environment or the original if no refinement is possible."
  [env var type positive?]
  (if-let [current-type (get env var)]
    (let [refined-type (if positive?
                         (intersect-types current-type type)
                         (type-difference current-type type))]
      ;; Only update if the refinement doesn't make the type bottom
      (if (= refined-type bottom-type)
        env
        (assoc env var refined-type)))
    ;; Variable not in environment
    env))

;; Apply a type constraint to the environment
(defn apply-constraint
  "Apply a type constraint to the environment."
  [env constraint positive?]
  (cond
    ;; Standard type constraint
    (type-constraint? constraint)
    (refine-env env (:var constraint) (:type constraint) positive?)

    ;; Equality between two variables - find common type
    (and (map? constraint) (:eq-vars constraint))
    (let [[var1 var2] (:eq-vars constraint)
          type1 (get env var1)
          type2 (get env var2)]
      (if (and type1 type2 positive?)
        ;; In positive context (equality is true), both vars must have the same type
        ;; so we refine each to their common type (intersection)
        (let [common-type (intersect-types type1 type2)]
          (if (= common-type bottom-type)
            ;; If no common type, return unchanged environment (this path is unreachable)
            env
            ;; Otherwise refine both variables
            (-> env
                (assoc var1 common-type)
                (assoc var2 common-type))))
        ;; In negative context (equality is false), we don't refine the types
        env))

    ;; Default case
    :else env))

;; Merge multiple environments
(defn merge-environments
  "Merge multiple environments by taking the union of types for each variable."
  [base-env & envs]
  (if (empty? envs)
    base-env
    (reduce (fn [result new-env]
              (merge-with (fn [t1 t2]
                            (if (= t1 t2)
                              t1
                              (union-type t1 t2)))
                          result
                          new-env))
            base-env
            envs)))

;; Determine formula type for dispatch
(defn formula-type [formula]
  (cond
    (or (true? formula) (false? formula)) :constant
    (type-constraint? formula) :type
    (and (map? formula) (:eq-vars formula)) :eq-vars
    (negation? formula) :negation
    (conjunction? formula) :conjunction
    (disjunction? formula) :disjunction
    :else :unknown))

;; Formula application strategies based on formula type
(def formula-application-strategies
  {;; Constants - identity function
   :constant   (fn [env _ _] env)

   ;; Type constraints
   :type       (fn [env formula positive?]
                 (apply-constraint env formula positive?))

   ;; Equality between variables
   :eq-vars    (fn [env formula positive?]
                 (apply-constraint env formula positive?))

   ;; Negation - invert positive flag
   :negation   (fn [env formula positive?]
                 (apply-formula env (:formula formula) (not positive?)))

   ;; Conjunction - apply each clause
   :conjunction (fn [env formula positive?]
                  (if positive?
                    ;; Conjunction in positive context - apply all clauses sequentially
                    (reduce (fn [curr-env clause]
                              (apply-formula curr-env clause true))
                            env
                            (:clauses formula))
                    ;; Conjunction in negative context - merge all branch environments
                    (apply merge-environments env
                           (map #(apply-formula env % false) (:clauses formula)))))

   ;; Disjunction - compute for each branch
   :disjunction (fn [env formula positive?]
                  (if positive?
                    ;; Disjunction in positive context - merge all branch environments
                    (apply merge-environments env
                           (map #(apply-formula env % true) (:clauses formula)))
                    ;; Disjunction in negative context - apply all clauses sequentially
                    (reduce (fn [curr-env clause]
                              (apply-formula curr-env clause false))
                            env
                            (:clauses formula))))})

;; Main formula application function
(defn apply-formula
  "Apply a boolean formula to an environment.
   Uses a data-driven approach to handle different formula types."
  [env formula positive?]
  (let [type (formula-type formula)]
    (if-let [strategy (get formula-application-strategies type)]
      (strategy env formula positive?)
      ;; Unknown formula type - return unchanged environment
      env)))

;;; ---- Testing ----

(defn -main [& args]
  (println "Simplified Occurrence Typing System")
  (println "To run the tests, use: lein test occur.core-logic-typing-test"))

;; Example of inter-procedural refinements using latent predicates
(defn example-interprocedural-refinements []
  (let [;; Define initial environment
        base-env {;; Fixed arity functions
                 'string-length (function-type [string-type] int-type)
                 ;; Operators
                 '< (function-type [int-type int-type] bool-type)
                 '> (function-type [int-type int-type] bool-type)
                 '= (function-type [any-type any-type] bool-type)
                 '+ (function-type [int-type int-type] int-type)
                 ;; Predicates with latent predicates
                 'number? (function-type [any-type] bool-type
                                        :latent-predicates {'x (type-constraint 'x int-type)})
                 'string? (function-type [any-type] bool-type
                                        :latent-predicates {'x (type-constraint 'x string-type)})
                 'boolean? (function-type [any-type] bool-type
                                         :latent-predicates {'x (type-constraint 'x bool-type)})}

        ;; Define a function that checks if a value is a number and doubles it if so
        double-if-number-def '(defn double-if-number [x]
                                (if (number? x)
                                  (+ x x)
                                  nil))

        ;; Add the function to environment
        env-with-func (typecheck base-env double-if-number-def)

        ;; Get the function's type
        double-func-type (get env-with-func 'double-if-number)

        ;; Define a function that uses double-if-number
        user-func-def '(defn process-value [x]
                         (let [result (double-if-number x)]
                           (if result
                             ;; result is guaranteed to be a number here due to latent predicates
                             (+ result 1)
                             "Not a number")))

        ;; Add to environment
        final-env (typecheck env-with-func user-func-def)

        ;; Get the user function's type
        user-func-type (get final-env 'process-value)]

    (println "Function type with latent predicates:")
    (println double-func-type)
    (println "\nLatent predicates enable the type checker to verify:")
    (println "1. When (number? x) is true, x is refined to type :int in double-if-number")
    (println "2. When double-if-number returns non-nil, the result has type :int")
    (println "3. This allows (+ result 1) to typecheck without explicit checks")

    ;; For reference, try typechecking specific uses
    (println "\nTypechecking (process-value 42):")
    (typecheck final-env '(process-value 42))

    (println "\nTypechecking (process-value \"hello\"):")
    (typecheck final-env '(process-value "hello"))))

;; Define initial environment
(defn init-env []
  {;; Fixed arity functions
   'string-length (function-type [string-type] int-type)

   ;; Operators with fixed arity of 2
   '< (function-type [int-type int-type] bool-type)  ;; Exactly 2 args
   '> (function-type [int-type int-type] bool-type)  ;; Exactly 2 args
   '= (function-type [any-type any-type] bool-type)  ;; Exactly 2 args
   '+ (function-type [int-type int-type] int-type)   ;; Exactly 2 args

   ;; Boolean operators
   'and (function-type [bool-type bool-type] bool-type)
   'or (function-type [bool-type bool-type] bool-type)
   'not (function-type [bool-type] bool-type)

   ;; Predicates with latent predicates for occurrence typing
   'number? (function-type [any-type] bool-type
                          :latent-predicates {'x (type-constraint 'x int-type)})
   'string? (function-type [any-type] bool-type
                          :latent-predicates {'x (type-constraint 'x string-type)})
   'boolean? (function-type [any-type] bool-type
                           :latent-predicates {'x (type-constraint 'x bool-type)})})

;;; ---- Main Typechecking ----

;; ----- #6: Cleanup Typecheck Implementation -----
;; Convert complex typecheck function into a cleaner multimethod design

;; Enhanced if typechecking with path-sensitivity
(defn typecheck-if-enhanced [env condition then-expr else-expr]
  (let [condition-type (typecheck env condition)]
    ;; Verify condition type is compatible with boolean
    (when-not (compatible-with-bool? condition-type)
      (throw (ex-info "If condition must be boolean compatible"
                     {:expr condition
                      :type condition-type})))

    ;; Extract constraint formula from condition
    (let [formula (extract-formula condition)
          ;; Compute types of branches with refined environments
          then-env (if formula
                     (apply-formula env formula true)
                     env)
          else-env (if formula
                     (apply-formula env formula false)
                     env)
          then-type (if then-expr (typecheck then-env then-expr) nil)
          else-type (if else-expr (typecheck else-env else-expr) nil)]

      ;; Determine result type based on branch types
      (cond
        (nil? then-type) else-type
        (nil? else-type) then-type
        :else (union-type then-type else-type)))))

;; Define the multimethod for typechecking different expression types
(defmulti typecheck-expr (fn [env expr]
                         (cond
                           (integer? expr) :integer
                           (string? expr) :string
                           (boolean? expr) :boolean
                           (keyword? expr) :keyword
                           (symbol? expr) :symbol
                           (seq? expr) (if (empty? expr)
                                       :empty-list
                                       (first expr))
                           :else :unknown)))

;; Handle primitive literals
(defmethod typecheck-expr :integer [_ _] int-type)
(defmethod typecheck-expr :string [_ _] string-type)
(defmethod typecheck-expr :boolean [_ _] bool-type)

;; Handle keywords (used for types in tests)
(defmethod typecheck-expr :keyword [_ expr] expr)

;; Handle variable references
(defmethod typecheck-expr :symbol [env expr]
  (if-let [type (get env expr)]
    type
    (throw (ex-info "Unbound variable" {:expr expr, :env env}))))

;; Handle empty lists
(defmethod typecheck-expr :empty-list [_ _]
  (throw (ex-info "Cannot typecheck empty expression" {:expr '()})))

;; Handle function expressions
(defmethod typecheck-expr 'fn [env [_ params & body]]
  (let [;; Verify parameters are in a vector
        _ (when-not (vector? params)
            (throw (ex-info "Function parameters must be in a vector" {:params params})))
        
        ;; Parse parameters and type annotations - now with direct type syntax
        param-data (loop [i 0, names [], types [], curr-env {}]
                     (if (>= i (count params))
                       {:names names, :types types, :env curr-env}
                       (let [item (nth params i)]
                         (if (symbol? item)
                           ;; Found a parameter name - check if it has a type annotation
                           (if (and (< (inc i) (count params))
                                    (or (keyword? (nth params (inc i)))   ; Direct keyword type
                                        (set? (nth params (inc i)))       ; Union type
                                        (and (list? (nth params (inc i))) ; Arrow type syntax
                                             (= (count (nth params (inc i))) 3)
                                             (= (second (nth params (inc i))) '->))))
                             ;; Yes, has direct type annotation
                             (let [type-anno (nth params (inc i))
                                   ;; Process arrow type if needed
                                   type-value (if (and (list? type-anno) (= (second type-anno) '->))
                                                ;; Create a function type for arrow syntax
                                                (let [param-type (typecheck env (first type-anno))
                                                      return-type (typecheck env (nth type-anno 2))]
                                                  (function-type [param-type] return-type))
                                                ;; Otherwise use direct type
                                                (typecheck env type-anno))]
                                 (recur (+ i 2)
                                      (conj names item)
                                      (conj types type-value)
                                      (assoc curr-env item type-value)))
                             ;; No type annotation
                             (recur (inc i)
                                    (conj names item)
                                    (conj types any-type)
                                    (assoc curr-env item any-type)))
                           ;; Skip non-symbol items
                           (recur (inc i) names types curr-env)))))
        
        param-names (:names param-data)
        param-types (:types param-data)
        param-env (:env param-data)
        
        ;; Combine with outer environment (for accessing outer scope)
        combined-env (merge param-env env)

        ;; Extract predicates from body expressions except the last one
        body-predicates (when (> (count body) 1)
                          (extract-formula (cons 'do (butlast body))))

        ;; Typecheck the body with parameters in scope
        return-type (typecheck combined-env (last body))

        ;; Extract latent predicates for parameters
        latent-preds (if body-predicates
                       {:body body-predicates}
                       {})]

    
    ;; Create and return the function type - pass the actual types, not names
    (function-type param-types return-type :latent-predicates latent-preds)))

;; Helper function to extract parameter-specific predicates
(defn extract-param-predicates [formula param-name]
  (cond
    ;; Check if formula is a type constraint for this parameter
    (and (map? formula)
         (= (:constraint formula) :type)
         (= (:var formula) param-name))
    formula

    ;; Check conjunction clauses
    (and (map? formula)
         (= (:constraint formula) :conjunction))
    (let [param-clauses (filter #(extract-param-predicates % param-name)
                               (:clauses formula))]
      (when (seq param-clauses)
        (if (= (count param-clauses) 1)
          (first param-clauses)
          (conjunction param-clauses))))

    ;; Check disjunction clauses
    (and (map? formula)
         (= (:constraint formula) :disjunction))
    (let [param-clauses (filter #(extract-param-predicates % param-name)
                               (:clauses formula))]
      (when (seq param-clauses)
        (if (= (count param-clauses) 1)
          (first param-clauses)
          (disjunction param-clauses))))

    ;; Check negation
    (and (map? formula)
         (= (:constraint formula) :negation))
    (when-let [inner (extract-param-predicates (:formula formula) param-name)]
      (negation inner))

    ;; Not a constraint involving this parameter
    :else nil))

;; Handle let expressions
(defmethod typecheck-expr 'let [env [_ bindings body]]
  (let [pairs (partition 2 bindings)
        ;; Create new environment with local bindings, evaluating each in the context
        ;; of previous bindings to allow references between bindings
        new-env (reduce (fn [e [var val-expr]]
                          (assoc e var (typecheck e val-expr)))
                        env
                        pairs)]
    ;; Typecheck body in the new environment
    (typecheck new-env body)))

;; Handle if expressions
(defmethod typecheck-expr 'if [env [_ condition then-expr else-expr]]
  (typecheck-if-enhanced env condition then-expr else-expr))

;; Handle union type special form
(defmethod typecheck-expr 'union [env [_ & type-exprs]]
  (if (empty? type-exprs)
    bottom-type  ;; Empty union is bottom type
    (let [;; Keep track of already typechecked expressions to prevent cycles
          checked-types (atom #{})
          
          ;; Process type expressions
          processed-types (map (fn [expr]
                               ;; Skip if we've seen this exact expression before
                               (if (contains? @checked-types expr)
                                 any-type
                                 (do
                                   ;; Mark as checked
                                   (swap! checked-types conj expr)
                                   (typecheck env expr))))
                             type-exprs)]
      ;; Create union from processed types
      (union-type processed-types))))

;; Handle boolean operations
(defmethod typecheck-expr 'and [env [_ & args]]
  ;; Check that all arguments are boolean compatible
  (doseq [arg args]
    (let [arg-type (typecheck env arg)]
      (when-not (compatible-with-bool? arg-type)
        (throw (ex-info "Arguments to 'and' must be boolean compatible"
                        {:expr arg :type arg-type})))))
  bool-type)

(defmethod typecheck-expr 'or [env [_ & args]]
  ;; Check that all arguments are boolean compatible
  (doseq [arg args]
    (let [arg-type (typecheck env arg)]
      (when-not (compatible-with-bool? arg-type)
        (throw (ex-info "Arguments to 'or' must be boolean compatible"
                        {:expr arg :type arg-type})))))
  bool-type)

(defmethod typecheck-expr 'not [env [_ arg]]
  (let [arg-type (typecheck env arg)]
    (when-not (compatible-with-bool? arg-type)
      (throw (ex-info "Argument to 'not' must be boolean compatible"
                      {:expr arg :type arg-type}))))
  bool-type)

;; Handle function applications (and operators)
(defmethod typecheck-expr :default [env [f & args]]
  (let [func-type (typecheck env f)]
    (cond
      ;; Special case for when recursion protection returns any-type
      (= func-type any-type)
      any-type
      
      ;; Check if it's a function type
      (function-type? func-type)
      (let [param-types (:param-types func-type)
            return-type (:return-type func-type)
            latent-predicates (:latent-predicates func-type)
            arg-types (mapv #(typecheck env %) args)]

        ;; Check argument count
        (when (not= (count param-types) (count args))
          (throw (ex-info (str (if (symbol? f)
                               (str (name f) " operator")
                               "Function")
                             " expects " (count param-types)
                             " arguments but got " (count args))
                        {:func f, :args args})))

        ;; Check argument types
        (doseq [[i [param-type arg-expr]] (map-indexed vector (map vector param-types args))]
          (let [arg-type (typecheck env arg-expr)]
            (when (and (not= arg-type any-type)  ;; Skip check if recursion protection returned any-type
                       (not (subtype? arg-type param-type)))
              (throw (ex-info (str (if (symbol? f)
                                   (str "Argument " (inc i) " to " (name f))
                                   "Argument")
                                 " type mismatch")
                            {:expected param-type
                             :actual arg-type
                             :expr arg-expr})))))

        ;; Apply latent predicates if present and track the refined environment
        (let [;; Create an environment with argument bindings (for substitution of parameter names)
              param-arg-map (zipmap (map symbol param-types) args)

              ;; Start with current environment
              refined-env (atom env)]

          ;; Apply parameter-specific latent predicates
          (doseq [[param-idx param-type] (map-indexed vector param-types)]
            (let [arg (nth args param-idx)
                  param-name (symbol param-type)]
              (when-let [param-pred (get latent-predicates param-name)]
                ;; Only proceed if the argument is a symbol (a variable)
                (when (symbol? arg)
                  ;; Create a substituted predicate where parameter name is replaced with argument name
                  (let [substituted-pred (substitute-var param-pred param-name arg)]
                    ;; Apply the substituted predicate to refine the argument's type
                    (swap! refined-env apply-formula substituted-pred true))))))

          ;; Apply body predicates if present
          (when-let [body-preds (:body latent-predicates)]
            ;; Create a substituted predicate where parameters are replaced with arguments
            (let [substituted-body-pred
                  (reduce-kv (fn [pred param-name arg]
                               (if (symbol? arg)
                                 (substitute-var pred param-name arg)
                                 pred))
                             body-preds
                             param-arg-map)]
              ;; Apply the substituted body predicates to the environment
              (swap! refined-env apply-formula substituted-body-pred true)))

          ;; Return the function's return type, possibly refined by latent predicates
          return-type))

      ;; Not a function
      :else
      (throw (ex-info "Applying a non-function"
                    {:expr f
                     :type func-type})))))

;; Helper function to substitute variable names in predicates
(defn substitute-var [formula old-var new-var]
  (cond
    ;; Type constraint - replace var name if it matches
    (and (map? formula)
         (= (:constraint formula) :type))
    (if (= (:var formula) old-var)
      (assoc formula :var new-var)
      formula)

    ;; Conjunction - recursively substitute in each clause
    (and (map? formula)
         (= (:constraint formula) :conjunction))
    (assoc formula
      :clauses
      (mapv #(substitute-var % old-var new-var) (:clauses formula)))

    ;; Disjunction - recursively substitute in each clause
    (and (map? formula)
         (= (:constraint formula) :disjunction))
    (assoc formula
      :clauses
      (mapv #(substitute-var % old-var new-var) (:clauses formula)))

    ;; Negation - recursively substitute in inner formula
    (and (map? formula)
         (= (:constraint formula) :negation))
    (assoc formula
      :formula
      (substitute-var (:formula formula) old-var new-var))

    ;; Other formula types or non-formulas - return unchanged
    :else formula))

;; Main typecheck entry point with recursion protection
(defn typecheck [env expr]
  (typecheck-expr env expr))

;; Handle named function definitions with type annotations
(defmethod typecheck-expr 'defn [env [_ name params & body]]
  (let [;; Check for docstring (skip if present)
        [docstring body] (if (string? (first body))
                           [(first body) (rest body)]
                           [nil body])

        ;; Check for return type annotation
        [return-type-expr body] (if (and (seq? (first body))
                                         (= (ffirst body) :->))
                                  [(second (first body)) (rest body)]
                                  [nil body])

        ;; Parse parameter types and collect latent predicate annotations
        param-info (loop [i 0
                          param-types []
                          param-names []
                          latent-preds {}]
                     (if (>= i (count params))
                       {:param-types param-types, :param-names param-names, :latent-predicates latent-preds}
                       (let [item (nth params i)]
                         (if (symbol? item)
                           ;; Found a parameter name
                           (if (and (< (inc i) (count params))
                                    (or (keyword? (nth params (inc i)))   ; Direct keyword type
                                        (set? (nth params (inc i)))       ; Union type
                                        (and (list? (nth params (inc i))) ; Arrow type syntax
                                             (= (count (nth params (inc i))) 3)
                                             (= (second (nth params (inc i))) '->))))
                             ;; Has direct type annotation
                             (let [param-name item
                                   type-anno (nth params (inc i))
                                   ;; Process arrow type if needed
                                   type-value (if (and (list? type-anno) (= (second type-anno) '->))
                                                ;; Create a function type for arrow syntax
                                                (let [param-type (typecheck env (first type-anno))
                                                      return-type (typecheck env (nth type-anno 2))]
                                                  (function-type [param-type] return-type))
                                                ;; Otherwise use direct type
                                                (typecheck env type-anno))]
                               (recur (+ i 2)
                                      (conj param-types type-value)
                                      (conj param-names param-name)
                                      latent-preds))
                             ;; No type annotation
                             (recur (inc i)
                                    (conj param-types any-type)
                                    (conj param-names item)
                                    latent-preds))
                           ;; Skip non-symbol items
                           (recur (inc i) param-types param-names latent-preds)))))

        param-types (:param-types param-info)
        param-names (:param-names param-info)
        latent-predicates (:latent-predicates param-info)
        
        ;; Create a placeholder function type to prevent infinite recursion
        placeholder-type (function-type
                          (vec (repeat (count param-types) any-type))
                          any-type)
                          
        ;; Add placeholder to environment to handle recursive functions
        env-with-placeholder (assoc env name placeholder-type)

        ;; Create environment with parameters for typechecking the body
        param-env (merge env-with-placeholder 
                         (zipmap param-names param-types))

        ;; Extract predicates from body expressions except the last one
        body-predicates (when (> (count body) 1)
                          (extract-formula (cons 'do (butlast body))))

        ;; Compute return type
        computed-return-type (typecheck param-env (last body))

        ;; Use explicitly provided return type or computed type
        final-return-type (if return-type-expr
                            (let [annot-type (typecheck env return-type-expr)]
                              (when-not (subtype? computed-return-type annot-type)
                                (throw (ex-info "Function return type doesn't match annotation"
                                                {:computed computed-return-type
                                                 :annotated annot-type})))
                              annot-type)
                            computed-return-type)

        ;; Combine all latent predicates
        all-latent-preds (cond-> latent-predicates
                           ;; Add body predicates if present
                           body-predicates
                           (assoc :body body-predicates))]

        
    ;; Create the function type
    (let [func-type (function-type
                     param-types
                     final-return-type
                     :latent-predicates all-latent-preds)]
      
      
      ;; Bind function name to its type in the environment
      (assoc env name func-type))))
