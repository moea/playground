(ns occur.core-logic-typing
  (:require [clojure.core.logic :as l]
            [clojure.set :as set]
            [occur.boolean-constraints :as bc]))

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
  {:type :function, :param-type param-type, :return-type return-type})

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

;;; ---- Core.Logic Constraint Solving ----

;; Define type predicates
(def predicate-type-map
  {'number? int-type
   'string? string-type
   'boolean? bool-type})

;; Initialize environment with primitives
(defn init-env []
  (merge
    {'string-length (function-type string-type int-type)
     '= (function-type any-type bool-type)}
    ;; Add predicates to environment as functions
    (reduce-kv (fn [env pred-name type]
                 (assoc env
                        pred-name
                        (function-type any-type bool-type)))
               {}
               predicate-type-map)))

;; Use core.logic to solve path constraints
(defn solve-path-constraints [env type-constraints]
  (if (empty? type-constraints)
    env
    (let [;; Extract variables and types from constraints
          vars (map :var type-constraints)
          types (map :type type-constraints)

          ;; Apply each constraint sequentially to refine types
          refined-env (reduce (fn [curr-env idx]
                                (let [var (nth vars idx)
                                      curr-type (get curr-env var)
                                      constraint-type (nth types idx)]
                                  (if curr-type
                                    ;; Refine the type with intersection
                                    (let [refined-type (intersect-types curr-type constraint-type)]
                                      (if (= refined-type bottom-type)
                                        ;; If bottom type, constraint can't be satisfied
                                        curr-env
                                        ;; Otherwise update the environment
                                        (assoc curr-env var refined-type)))
                                    ;; If variable not in environment, keep env unchanged
                                    curr-env)))
                              env
                              (range (count vars)))]
      refined-env)))

;; Solve negated path constraints
(defn solve-negated-constraints [env type-constraints]
  (if (empty? type-constraints)
    env
    (let [;; Create negated constraints by computing type difference
          negated-constraints
          (filter identity
                  (map (fn [c]
                         (let [var (:var c)
                               curr-type (get env var)
                               constraint-type (:type c)]
                           (when curr-type
                             {:var var
                              :type (type-difference curr-type constraint-type)})))
                       type-constraints))]
      ;; Apply the negated constraints
      (solve-path-constraints env negated-constraints))))

;;; ---- Macros and Expansion ----

;; Macros for boolean operations
(def macros
  {'and (fn [& args]
          (if (empty? args)
            true
            (if (= (count args) 1)
              (first args)
              (list 'if (first args)
                    (apply (get macros 'and) (rest args))
                    false))))
   'or  (fn [& args]
          (if (empty? args)
            false
            (if (= (count args) 1)
              (first args)
              (list 'if (first args)
                    true
                    (apply (get macros 'or) (rest args))))))
   'not (fn [x] (list 'if x false true))})

;; Simple macroexpander
(defn expand-1 [form]
  (if (and (seq? form) (symbol? (first form)))
    (let [macro-fn (get macros (first form))]
      (if macro-fn
        (apply macro-fn (rest form))
        form))
    form))

;; Full recursive macroexpansion
(defn expand-all [form]
  (let [expanded (expand-1 form)]
    (if (= expanded form)
      (if (seq? form)
        (apply list (map expand-all form))
        form)
      (expand-all expanded))))

;;; ---- Constraint Extraction ----

;; Extract type predicates
(defn extract-predicate [expr]
  (when (and (seq? expr) (symbol? (first expr)))
    (when-let [type (get predicate-type-map (first expr))]
      (when (= (count expr) 2)
        {:var (second expr) :type type}))))

;; Extract constraints from expressions for core.logic
(defn extract-constraints [expr]
  (cond
    ;; Literal values - no constraints
    (or (integer? expr) (string? expr) (boolean? expr))
    []

    ;; Variable reference - no constraints
    (symbol? expr)
    []

    ;; Sequence expressions
    (seq? expr)
    (case (first expr)
      ;; Direct 'not' application to predicate
      not (if-let [pred (extract-predicate (second expr))]
            [{:op :not :var (:var pred) :type (:type pred)}]
            (mapcat extract-constraints (rest expr)))

      ;; 'and' expression
      and (let [inner-constraints (mapcat extract-constraints (rest expr))]
            (if (> (count inner-constraints) 1)
              [{:op :and :constraints inner-constraints}]
              inner-constraints))

      ;; 'or' expression
      or (let [inner-constraints (mapcat extract-constraints (rest expr))]
           (if (> (count inner-constraints) 1)
             [{:op :or :constraints inner-constraints}]
             inner-constraints))

      ;; If expression - extract from condition
      if (extract-constraints (second expr))

      ;; Type predicate
      (if-let [pred (extract-predicate expr)]
        [{:op :is :var (:var pred) :type (:type pred)}]

        ;; Other expressions
        (mapcat extract-constraints (rest expr))))

    ;; Default
    :else []))

;; Process complex constraints into simple positive constraints
(defn flatten-constraints [constraints positive?]
  (if (empty? constraints)
    []
    (mapcat (fn [c]
              (case (:op c)
                :is (if positive?
                      [{:var (:var c) :type (:type c)}]
                      [])
                :not (flatten-constraints [{:op :is :var (:var c) :type (:type c)}] (not positive?))
                :and (if positive?
                       ;; For AND in positive path, flatten all constraints
                       (flatten-constraints (:constraints c) positive?)
                       ;; For AND in negative path, De Morgan: !(A && B) = !A || !B
                       ;; We can't express OR constraints in simple form, skip for now
                       [])
                :or (if positive?
                      ;; For OR in positive path, we can't flatten easily
                      ;; This is a limitation - ideally we'd have separate environments
                      ;; for each branch of the OR
                      []
                      ;; For OR in negative path, De Morgan: !(A || B) = !A && !B
                      ;; So we can flatten all constraints with negated positive?
                      (flatten-constraints
                       (mapv (fn [sub-c]
                               (case (:op sub-c)
                                 :is {:op :not :var (:var sub-c) :type (:type sub-c)}
                                 :not {:op :is :var (:var sub-c) :type (:type sub-c)}
                                 sub-c))
                             (:constraints c))
                       true))))
            constraints)))

;;; ---- Typechecking with Core.Logic ----

;; Forward declaration for mutual recursion
(declare typecheck)

;; Special handling for negation of string? and other direct type predicates
(defn handle-direct-negation [env expr]
  (if (and (seq? expr)
           (= (first expr) 'if)
           (= (count expr) 4))
    (let [condition (second expr)
          then-val (nth expr 2)
          else-val (nth expr 3)]
      (if (and (seq? condition)
               (= (count condition) 2)
               (contains? (set (keys predicate-type-map)) (first condition))
               (= then-val false)
               (= else-val true))
        ;; This is a direct negation pattern (if (pred x) false true)
        (let [var (second condition)
              pred-type (get predicate-type-map (first condition))
              current-type (get env var)]
          (if current-type
            ;; Remove the predicate type from the current type
            (let [negated-type (type-difference current-type pred-type)]
              (if (= negated-type bottom-type)
                env
                (assoc env var negated-type)))
            env))
        env))
    env))

;; Enhanced if expression handler using core.logic
(defn typecheck-if-enhanced [env condition then-expr else-expr]
  (let [;; Expand macros in the condition
        expanded-condition (expand-all condition)
        _ (println "Expanded:" expanded-condition)

        ;; Extract constraints
        constraints (extract-constraints expanded-condition)
        _ (println "Constraints:" constraints)

        ;; Check condition type
        condition-type (typecheck env expanded-condition)

        ;; Special handling for direct negations (not (string? x))
        modified-env (if (and (seq? expanded-condition)
                              (= (first expanded-condition) 'if))
                       (handle-direct-negation env expanded-condition)
                       env)

        ;; Process constraints for the positive (then) branch
        positive-constraints (flatten-constraints constraints true)
        _ (println "Positive constraints:" positive-constraints)

        ;; Process constraints for the negative (else) branch
        negative-constraints (flatten-constraints constraints false)
        _ (println "Negative constraints:" negative-constraints)

        ;; Special handling for (not (or a b)) pattern in 6th test
        negated-or-constraints
        (if (and (seq? expanded-condition)
                 (= (count expanded-condition) 2)
                 (= (first expanded-condition) 'not)
                 (seq? (second expanded-condition))
                 (= (first (second expanded-condition)) 'or))
          ;; This is form (not (or A B ...))
          (let [or-args (rest (second expanded-condition))
                or-constraints (mapcat extract-constraints or-args)]
            ;; For !(A || B), we need !A && !B
            (mapcat (fn [c]
                      (case (:op c)
                        :is [{:var (:var c) :type (type-difference (get env (:var c)) (:type c))}]
                        :not [{:var (:var c) :type (:type c)}]
                        []))
                    or-constraints))
          [])

        ;; Apply constraints using core.logic
        then-env (if (not-empty positive-constraints)
                   (solve-path-constraints modified-env positive-constraints)
                   modified-env)
        else-env (if (not-empty negative-constraints)
                   (solve-path-constraints modified-env
                                           (concat negative-constraints negated-or-constraints))
                   modified-env)

        ;; Typecheck each branch
        then-type (typecheck then-env then-expr)
        else-type (if else-expr (typecheck else-env else-expr) nil)]
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

    ;; If expression with core.logic constraint solving
    (and (seq? expr) (= (first expr) 'if))
    (typecheck-if-enhanced env (nth expr 1) (nth expr 2) (nth expr 3 nil))

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
    (let [expanded (expand-all expr)
          env (init-env)
          result-type (typecheck env expanded)]
      (println "Result type:" result-type))
    (catch Exception e
      (println "Type error:" (.getMessage e))
      (println "  Details:" (ex-data e)))))

;;; ---- Integration with Boolean Constraint Solver ----

;; Initialize the boolean constraint solver with our type system functions
(def boolean-constraint-solver
  (bc/create-boolean-constraint-solver subtype? intersect-types type-difference union-type))

;; Enhanced if expression handler using boolean constraint solver
(defn typecheck-if-with-boolean-solver [env condition then-expr else-expr]
  (let [;; Expand macros in the condition
        expanded-condition (expand-all condition)
        _ (println "Expanded:" expanded-condition)

        ;; Check condition type
        condition-type (typecheck env expanded-condition)

        ;; Check if there's an equality expression that needs special handling
        has-equality (and (seq? expanded-condition)
                          (= (count expanded-condition) 3)
                          (= (first expanded-condition) '=))

        ;; Use the boolean constraint solver
        then-env (try
                   (boolean-constraint-solver env expanded-condition true)
                   (catch Exception e
                     (println "Warning: Boolean solver failed for then branch:" (.getMessage e))
                     ;; Special handling for equality expressions
                     (if has-equality
                       (let [var (second expanded-condition)
                             val (nth expanded-condition 2)
                             var-type (get env var)]
                         ;; Only refine if it's a boolean value we're comparing with
                         (if (and (boolean? val) (not (nil? var-type)))
                           (assoc env var bool-type)
                           env))
                       env)))
        else-env (try
                   (boolean-constraint-solver env expanded-condition false)
                   (catch Exception e
                     (println "Warning: Boolean solver failed for else branch:" (.getMessage e))
                     ;; Special handling for equality expressions
                     (if has-equality
                       (let [var (second expanded-condition)
                             val (nth expanded-condition 2)
                             var-type (get env var)]
                         ;; Only refine if it's a boolean value we're comparing with
                         (if (and (boolean? val) (not (nil? var-type)))
                           (assoc env var bool-type)
                           env))
                       env)))

        ;; Typecheck each branch
        then-type (typecheck then-env then-expr)
        else-type (if else-expr (typecheck else-env else-expr) nil)]
    (if (compatible-with-bool? condition-type)
      (union-type (remove nil? [then-type else-type]))
      (throw (ex-info "Condition must be a boolean-compatible type"
                      {:expr condition :type condition-type})))))

;; Enhanced analysis function using boolean constraint solver
(defn analyze-expr-boolean [expr]
  (println "\nAnalyzing expression with boolean solver:")
  (println expr)
  (try
    (let [expanded (expand-all expr)
          env (init-env)
          ;; Use specialized typecheck function with boolean solver for if expressions
          result-type ((fn typecheck-with-boolean [env expr]
                         (if (and (seq? expr) (= (first expr) 'if))
                           (typecheck-if-with-boolean-solver env (nth expr 1) (nth expr 2) (nth expr 3 nil))
                           (typecheck env expr)))
                       env expanded)]
      (println "Result type:" result-type))
    (catch Exception e
      (println "Type error:" (.getMessage e))
      (println "  Details:" (ex-data e)))))

;; Test the solver with full boolean constraint handling
(defn test-boolean-constraint-solver []
  (println "\n=== OCCURRENCE TYPING WITH FULL BOOLEAN CONSTRAINT SOLVING ===\n")

  ;; Simple negation - should properly handle the types
  (analyze-expr-boolean '(let [x (union 42 "hello" true)]
                           (if (not (string? x))
                             "not a string"
                             (string-length x))))

  ;; Complex case from test 6 - properly handle nested not-or
  (analyze-expr-boolean '(let [x (union 42 "hello" true)]
                           (if (not (or (number? x) (boolean? x)))
                             (string-length x)  ;; must be a string here
                             "not a string")))

  ;; Nested chains with multiple ANDs and ORs
  (analyze-expr-boolean '(let [x (union 42 "hello" true false)]
                           (if (and (not (number? x))
                                    (or (string? x)
                                        (and (boolean? x) (not (= x false)))))
                             "refined correctly"
                             "fallback")))


  (println "\nBoolean constraint tests completed."))

;; Update the main test function to include boolean constraint solver tests
(defn test-occurrence-typing []
  (println "\n=== OCCURRENCE TYPING WITH CORE.LOGIC ===\n")

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

  ;; Run tests with full boolean constraint solver
  (test-boolean-constraint-solver))

;; Run tests
(test-occurrence-typing)
