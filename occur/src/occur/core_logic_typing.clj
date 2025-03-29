(ns occur.core-logic-typing
  (:require [clojure.core.logic :as l]
            [clojure.set :as set]
            [occur.boolean-constraints :as bc :refer
             [Conjunction? Disjunction? Negation? TypeConstraint?]])
  (:import [occur.boolean_constraints TypeConstraint Negation Conjunction Disjunction]))

;;; ---- Type System Core ----

;; Basic primitive types
(def int-type :int)
(def string-type :string)
(def bool-type :bool)
(def any-type :any)
(def bottom-type :bottom)

;; Type constructors and predicates
(defn union-type [types]
  (let [flattened (reduce (fn [acc t]
                            (if (and (map? t) (= (:type t) :union))
                              (set/union acc (:types t))
                              (conj acc t)))
                          #{}
                          types)]
    (cond
      (empty? flattened) bottom-type
      (= (count flattened) 1) (first flattened)
      :else {:type :union, :types flattened})))

(defn function-type [param-type return-type]
  {:type :function :param-type param-type, :return-type return-type})

(defn function-type? [t]
  (and (map? t) (= (:type t) :function)))

;; Subtyping and type compatibility functions
(defn subtype? [sub-type super-type]
  (cond
    ;; Any type is a supertype of all types
    (= super-type any-type) true

    ;; Bottom type is a subtype of all types
    (= sub-type bottom-type) true

    ;; Same types
    (= sub-type super-type) true

    ;; Union types - sub-type must be a subset of super-type
    (and (map? super-type) (= (:type super-type) :union))
    (if (map? sub-type)
      (if (= (:type sub-type) :union)
        (every? (fn [t] (subtype? t super-type)) (:types sub-type))
        false)
      (contains? (:types super-type) sub-type))

    ;; Subtype is a union type
    (and (map? sub-type) (= (:type sub-type) :union))
    (every? (fn [t] (subtype? t super-type)) (:types sub-type))

    ;; Function subtyping - contravariant in parameter type, covariant in return type
    (and (function-type? sub-type) (function-type? super-type))
    (and (subtype? (:param-type super-type) (:param-type sub-type))
         (subtype? (:return-type sub-type) (:return-type super-type)))

    :else false))

(defn intersect-types [t1 t2]
  (cond
    ;; Bottom type intersection with anything is bottom
    (or (= t1 bottom-type) (= t2 bottom-type)) bottom-type

    ;; Any type intersection is the other type
    (= t1 any-type) t2
    (= t2 any-type) t1

    ;; Same type
    (= t1 t2) t1

    ;; Intersection with a union type
    (and (map? t1) (= (:type t1) :union))
    (let [intersected (filter (fn [t] (not= (intersect-types t t2) bottom-type))
                              (:types t1))]
      (if (empty? intersected)
        bottom-type
        (union-type intersected)))

    (and (map? t2) (= (:type t2) :union))
    (intersect-types t2 t1)

    ;; Otherwise, if types don't match and neither is a union, no intersection
    :else bottom-type))

(defn type-difference [t1 t2]
  (cond
    ;; Removing from bottom type is still bottom
    (= t1 bottom-type) bottom-type

    ;; Removing bottom type doesn't change anything
    (= t2 bottom-type) t1

    ;; Removing from any type is complex, we don't handle this directly
    (= t1 any-type) any-type

    ;; Difference with same type is bottom
    (= t1 t2) bottom-type

    ;; Difference with a union type on left
    (and (map? t1) (= (:type t1) :union))
    (let [diff-types (filter (fn [t] (not= (intersect-types t t2) t))
                             (:types t1))]
      (if (empty? diff-types)
        bottom-type
        (union-type diff-types)))

    ;; Difference with a union type on right
    (and (map? t2) (= (:type t2) :union))
    (let [remaining-type (reduce (fn [curr-type remove-type]
                                   (type-difference curr-type remove-type))
                                 t1
                                 (:types t2))]
      remaining-type)

    ;; Simple types that don't match - no change
    :else t1))

(defn compatible-with-bool? [t]
  (or (= t bool-type)
      (and (map? t) (= (:type t) :union) (contains? (:types t) bool-type))))

;;; ---- Constraint System ----

;; Define type predicates
(def predicate-type-map
  {'number? int-type
   'string? string-type
   'boolean? bool-type})

;; Initialize environment with primitives
(defn init-env []
  (merge
    {'string-length (function-type string-type int-type)
     '= (function-type any-type bool-type)
     'and (function-type bool-type bool-type)
     'or (function-type bool-type bool-type)
     'not (function-type bool-type bool-type)}
    ;; Add predicates to environment as functions
    (reduce-kv (fn [env pred-name type]
                 (assoc env
                        pred-name
                        (function-type any-type bool-type)))
               {}
               predicate-type-map)))

;;; ---- Boolean Formula Adaptation ----

;; Initialize the boolean constraint solver with our type system functions
(def boolean-constraint-solver
  (bc/create-boolean-constraint-solver subtype? intersect-types type-difference union-type))

;; Helper functions to adapt between our typesystem and boolean_constraints.clj

(defn get-predicate-var [formula]
  (:var formula))

(defn get-predicate-type [formula]
  (:type formula))

(defn get-negation-formula [formula]
  (:formula formula))

(defn get-conjunction-clauses [formula]
  (:clauses formula))

(defn get-disjunction-clauses [formula]
  (:clauses formula))

;;; ---- Extract Constraints From Expressions ----

;; Extract a predicate from an expression
(defn extract-predicate [expr]
  (when (and (seq? expr) (symbol? (first expr)))
    (when-let [type (get predicate-type-map (first expr))]
      (when (= (count expr) 2)
        (bc/make-type-constraint (second expr) type)))))

;; Extract boolean formula from expression
(defn extract-formula [expr]
  (cond
    ;; Literal values - no constraints
    (or (integer? expr) (string? expr) (boolean? expr))
    nil

    ;; Variable reference - no constraints
    (symbol? expr)
    nil

    ;; Sequence expressions
    (seq? expr)
    (let [op   (first expr)
          args (rest expr)]
      (case op
        ;; Boolean operations
        not (when-let [inner (extract-formula (first args))]
              (bc/make-negation inner))

        and (let [inner-formulas (keep extract-formula args)]
              (if (seq inner-formulas)
                (bc/make-conjunction inner-formulas)
                nil))

        or (let [inner-formulas (keep extract-formula args)]
             (if (seq inner-formulas)
               (bc/make-disjunction inner-formulas)
               nil))

        ;; If expression - extract from condition
        if (extract-formula (first args))

        ;; Type predicate
        (if-let [pred (extract-predicate expr)]
          pred
          ;; Other expressions - try args recursively
          (let [inner-formulas (keep extract-formula args)]
            (if (= (count inner-formulas) 1)
              (first inner-formulas)
              (when (seq inner-formulas)
                (bc/make-conjunction inner-formulas)))))))

    ;; Default
    :else nil))

;; Apply type refinement for a single predicate
(defn apply-predicate [env positive? var type]
  (if-let [curr-type (get env var)]
    (let [refined-type (if positive?
                         (intersect-types curr-type type)
                         (type-difference curr-type type))]
      (if (= refined-type bottom-type)
        ;; Constraint cannot be satisfied
        env
        (assoc env var refined-type)))
    ;; Variable not in environment
    env))

;; Apply boolean formula to refine environment
(defn apply-formula [env formula positive?]
  (cond
    ;; Boolean constants
    (= formula true)  env
    (= formula false) env

    ;; Single predicate
    (TypeConstraint? formula)
    (apply-predicate env positive? (get-predicate-var formula) (get-predicate-type formula))

    ;; Negated predicate
    (and (Negation? formula) (TypeConstraint? (get-negation-formula formula)))
    (let [pred (get-negation-formula formula)]
      (apply-predicate env (not positive?) (get-predicate-var pred) (get-predicate-type pred)))

    ;; Conjunction
    (Conjunction? formula)
    (if positive?
      ;; All clauses must be satisfied in positive mode
      (reduce (fn [curr-env clause]
                (apply-formula curr-env clause true))
              env
              (get-conjunction-clauses formula))
      ;; In negative mode, we'd need separate environments for each clause negation
      ;; This is an approximation
      env)

    ;; Disjunction
    (Disjunction? formula)
    (if positive?
      ;; In positive mode, we'd need separate environments for each clause
      ;; This is an approximation
      env
      ;; In negative mode, all negated clauses must be satisfied (De Morgan)
      (reduce (fn [curr-env clause]
                (apply-formula curr-env clause false))
              env
              (get-disjunction-clauses formula)))

    ;; Default
    :else env))

;;; ---- Typechecking with Boolean Formulas ----

;; Forward declaration for mutual recursion
(declare typecheck)

;; Enhanced if expression handler using boolean formulas
(defn typecheck-if-enhanced [env condition then-expr else-expr]
  (let [;; First typecheck the condition itself
        condition-type (typecheck env condition)

        ;; Extract and normalize formula
        raw-formula (extract-formula condition)
        formula (when raw-formula (bc/to-nnf raw-formula))

        ;; Refine environment for both branches
        then-env (if formula
                   (apply-formula env formula true)
                   env)
        else-env (if formula
                   (apply-formula env (bc/make-negation formula) true)
                   env)

        ;; Typecheck branches with refined environments
        then-type (typecheck then-env then-expr)
        else-type (if else-expr
                    (typecheck else-env else-expr)
                    nil)]

    ;; Result is the union of both branch types
    (if (compatible-with-bool? condition-type)
      (union-type (remove nil? [then-type else-type]))
      (throw (ex-info "Condition must be a boolean-compatible type"
                      {:expr condition :type condition-type})))))

;; Core typechecking function
(defn typecheck [env expr]
  (cond
    ;; Integer literal
    (integer? expr) int-type

    ;; Boolean literal
    (boolean? expr) bool-type

    ;; String literal
    (string? expr) string-type

    ;; Variable reference
    (symbol? expr) (if-let [t (get env expr)]
                     t
                     (throw (ex-info (str "Unbound variable: " expr)
                                    {:expr expr :env env})))

    ;; Let expression: (let [x e1] e2)
    (and (seq? expr) (= (first expr) 'let))
    (let [bindings (second expr)
          body (nth expr 2)]
      (if (and (vector? bindings) (even? (count bindings)))
        (loop [remaining-bindings bindings
               new-env env]
          (if (empty? remaining-bindings)
            (typecheck new-env body)
            (let [var-name (first remaining-bindings)
                  var-expr (second remaining-bindings)
                  var-type (typecheck env var-expr)]
              (recur (drop 2 remaining-bindings)
                     (assoc new-env var-name var-type)))))
        (throw (ex-info "Invalid let bindings" {:expr expr}))))

    ;; Union type annotation: (union t1 t2 ...)
    (and (seq? expr) (= (first expr) 'union))
    (let [types (map #(typecheck env %) (rest expr))]
      (union-type types))

    ;; If expression with boolean formula constraint solving
    (and (seq? expr) (= (first expr) 'if))
    (typecheck-if-enhanced env (nth expr 1) (nth expr 2) (nth expr 3 nil))

    ;; Special handling for boolean operators
    (and (seq? expr) (= (first expr) 'and))
    (do
      ;; Type check all arguments
      (doseq [arg (rest expr)]
        (let [arg-type (typecheck env arg)]
          (when-not (compatible-with-bool? arg-type)
            (throw (ex-info "Arguments to 'and' must be boolean compatible"
                           {:expr arg :type arg-type})))))
      ;; Return boolean type
      bool-type)

    (and (seq? expr) (= (first expr) 'or))
    (do
      ;; Type check all arguments
      (doseq [arg (rest expr)]
        (let [arg-type (typecheck env arg)]
          (when-not (compatible-with-bool? arg-type)
            (throw (ex-info "Arguments to 'or' must be boolean compatible"
                           {:expr arg :type arg-type})))))
      ;; Return boolean type
      bool-type)

    (and (seq? expr) (= (first expr) 'not))
    (let [arg (second expr)
          arg-type (typecheck env arg)]
      (when-not (compatible-with-bool? arg-type)
        (throw (ex-info "Argument to 'not' must be boolean compatible"
                       {:expr arg :type arg-type})))
      ;; Return boolean type
      bool-type)

    ;; Function application: (f arg1 arg2 ...)
    (and (seq? expr) (not-empty expr))
    (let [fn-expr (first expr)
          args (rest expr)]
      (cond
        ;; Handle built-in operators that accept two arguments
        (contains? #{'< '> '+ '=} fn-expr)
        (if (= (count args) 2)
          (let [arg1-type (typecheck env (first args))
                arg2-type (typecheck env (second args))]
            ;; Return appropriate return type based on the operator
            (case fn-expr
              < bool-type
              > bool-type
              = bool-type
              + (if (and (subtype? arg1-type int-type)
                        (subtype? arg2-type int-type))
                 int-type
                 (throw (ex-info "Arguments to + must be numbers"
                                {:arg1-type arg1-type
                                 :arg2-type arg2-type})))))
          (throw (ex-info (str fn-expr " requires exactly 2 arguments")
                         {:expr expr})))

        ;; For all other function applications
        :else
        (let [fn-type (typecheck env fn-expr)]
          (if (function-type? fn-type)
            (if (= (count args) 1)
              (let [arg-expr (first args)
                    arg-type (typecheck env arg-expr)]
                (if (subtype? arg-type (:param-type fn-type))
                  (:return-type fn-type)
                  (throw (ex-info "Argument type doesn't match parameter type"
                                 {:fn-type fn-type
                                  :arg-type arg-type}))))
              (throw (ex-info "Function application with multiple arguments not supported"
                            {:expr expr})))
            (throw (ex-info "Applying a non-function"
                          {:expr expr
                           :fn-type fn-type}))))))

    :else (throw (ex-info (str "Unsupported expression: " expr)
                         {:expr expr}))))

;;; ---- Testing ----

(defn analyze-expr [expr]
  (println "\nAnalyzing expression:" expr)
  (try
    (let [env (init-env)
          result-type (typecheck env expr)]
      (println "Result type:" result-type))
    (catch Exception e
      (println "Type error:" (.getMessage e))
      (println "  Details:" (ex-data e)))))

;; Test the symbolic boolean expression typechecking
(defn test-boolean-constraint-solver []
  (println "\n=== OCCURRENCE TYPING WITH SYMBOLIC BOOLEAN EXPRESSIONS ===\n")

  ;; Simple negation - should properly handle the types
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (not (string? x))
                     "not a string"
                     (string-length x))))

  ;; Complex case - properly handle nested not-or
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (not (or (number? x) (boolean? x)))
                     (string-length x)  ;; must be a string here
                     "not a string")))

  ;; Nested chains with multiple ANDs and ORs
  (analyze-expr '(let [x (union 42 "hello" true false)]
                   (if (and (not (number? x))
                            (or (string? x)
                                (and (boolean? x) (not (= x false)))))
                     "refined correctly"
                     "fallback")))

  ;; Triple negation test - should properly handle
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (not (not (not (string? x))))
                     "triple negation"
                     (string-length x))))

  (println "\nBoolean expression tests completed."))

;; Main test function
(defn test-occurrence-typing []
  (println "\n=== OCCURRENCE TYPING WITH SYMBOLIC BOOLEAN EXPRESSIONS ===\n")

  ;; Basic type predicate
  (analyze-expr '(let [x (union 42 "hello")]
                   (if (string? x)
                     (string-length x)
                     0)))

  ;; Direct negation with not
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (not (string? x))
                     "not a string"
                     (string-length x))))

  ;; Compound expressions with OR
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (or (number? x) (string? x))
                     "number or string"
                     "boolean")))

  ;; Compound expressions with AND
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (and (string? x) (not (boolean? x)))
                     (string-length x)
                     "not a valid string")))

  ;; Complex nested boolean expressions
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (or (number? x)
                           (and (string? x) (not (boolean? x))))
                     "valid input"
                     "invalid input")))

  ;; Nested refinements with negation
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (not (or (number? x) (boolean? x)))
                     (string-length x)  ;; must be a string here
                     "not a string")))

  ;; Multiple arguments for AND
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (and (not (boolean? x)) (not (number? x)) (string? x))
                     (string-length x)
                     0)))

  ;; Multiple arguments for OR
  (analyze-expr '(let [x (union 42 "hello" true false)]
                   (if (or (number? x) (string? x) (boolean? x))
                     "known type"
                     "unknown type")))

  ;; Complex nested expression with multiple arguments
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (and (not (number? x))
                            (or (string? x) (boolean? x))
                            (not (and (boolean? x) (string? x))))
                     "valid refined type"
                     "invalid type")))

  (println "\nStandard tests completed.")

  ;; Run detailed tests with boolean expressions
  (test-boolean-constraint-solver))

;; Run tests
(test-occurrence-typing)
