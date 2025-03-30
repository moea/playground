(ns occur.core-logic-typing
  (:require [clojure.set :as set]))

;;; ---- Type System Core ----

;; Basic primitive types
(def int-type :int)
(def string-type :string)
(def bool-type :bool)
(def any-type :any)
(def bottom-type :bottom)

;; Forward declarations to avoid circular dependencies
(declare typecheck apply-formula extract-formula)

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
  "Create a function type with given param-types and return-type"
  [param-types return-type]
  {:type :function
   :param-types param-types
   :return-type return-type})

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

                         ;; var = var or other cases not handled
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
            (and (map? extract-result) (= (:type pred-info) :dynamic))
            (when-let [var-type (literal-type (:literal extract-result))]
              (type-constraint (:var extract-result) var-type))

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
  (if (type-constraint? constraint)
    (refine-env env (:var constraint) (:type constraint) positive?)
    env))

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

   ;; Predicates
   'number? (function-type [any-type] bool-type)
   'string? (function-type [any-type] bool-type)
   'boolean? (function-type [any-type] bool-type)})

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

;; Handle let expressions
(defmethod typecheck-expr 'let [env [_ bindings body]]
  (let [pairs (partition 2 bindings)
        ;; Create new environment with local bindings
        new-env (reduce (fn [e [var val-expr]]
                          (assoc e var (typecheck env val-expr)))
                        env
                        pairs)]
    ;; Typecheck body in the new environment
    (typecheck new-env body)))

;; Handle if expressions
(defmethod typecheck-expr 'if [env [_ condition then-expr else-expr]]
  (typecheck-if-enhanced env condition then-expr else-expr))

;; Handle union type special form
(defmethod typecheck-expr 'union [_ [_ & types]]
  (union-type types))

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
    (if (function-type? func-type)
      (let [param-types (:param-types func-type)
            return-type (:return-type func-type)]
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
            (when-not (subtype? arg-type param-type)
              (throw (ex-info (str (if (symbol? f)
                                     (str "Argument " (inc i) " to " (name f))
                                     "Argument")
                                   " type mismatch")
                              {:expected param-type
                               :actual arg-type
                               :expr arg-expr})))))

        ;; Return the function's return type
        return-type)

      ;; Not a function
      (throw (ex-info "Applying a non-function"
                      {:expr f
                       :type func-type})))))

;; Main typecheck entry point
(defn typecheck [env expr]
  (typecheck-expr env expr))
