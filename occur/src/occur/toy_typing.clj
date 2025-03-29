(ns occur.toy-typing
  (:require [clojure.set :as set]))

;; Type definitions
(def int-type :int)
(def bool-type :bool)
(def string-type :string)
(def any-type :any)  ;; Top type - all values have this type
(def nil-type {:type :nil})  ;; Define nil type for optional else clauses

(declare union-type?)

;; Type constructor for union types
(defn union-type [types]
  (let [types-set (set types)]
    (if (= (count types-set) 1)
      (first types-set)  ;; Simplify singleton unions
      {:type :union
       :types types-set})))

(defn union-merge [t1 t2]
  (cond (and (union-type? t1)
             (union-type? t2)) (union-type (into (:types t1) (:types t2)))
        (union-type? t1)       (union-type (conj (:types t1) t2))
        (union-type? t2)       (union-type (conj (:types t2) t1))
        :else                  (union-type [t1 t2])))

;; Type constructor for function types
(defn function-type [param-type return-type]
  {:type :function
   :param-type param-type
   :return-type return-type})

;; Type predicates
(defn int-type? [t] (= t int-type))
(defn bool-type? [t] (= t bool-type))
(defn string-type? [t] (= t string-type))
(defn any-type? [t] (= t any-type))
(defn union-type? [t] (and (map? t) (= (:type t) :union)))
(defn function-type? [t] (and (map? t) (= (:type t) :function)))

;; Type equality and subtyping
(defn type-equal? [t1 t2]
  (cond
    (and (keyword? t1) (keyword? t2)) (= t1 t2)
    (and (union-type? t1) (union-type? t2)) (= (:types t1) (:types t2))
    (and (function-type? t1) (function-type? t2))
    (and (type-equal? (:param-type t1) (:param-type t2))
         (type-equal? (:return-type t1) (:return-type t2)))
    :else false))

(defn subtype? [t1 t2]
  (cond
    (type-equal? t1 t2) true
    (any-type? t2) true  ;; Any type is a subtype of the any-type (top type)
    (union-type? t2) (if (union-type? t1)
                       (every? (fn [t] (some #(subtype? t %) (:types t2))) (:types t1))
                       (some #(subtype? t1 %) (:types t2)))
    (union-type? t1) (every? #(subtype? % t2) (:types t1))
    (and (function-type? t1) (function-type? t2))
    (and (subtype? (:param-type t2) (:param-type t1))  ; Contravariant in param type
         (subtype? (:return-type t1) (:return-type t2))) ; Covariant in return type
    :else false))

;; Type operations
(defn remove-type [union-t removed-t]
  (if (union-type? union-t)
    (let [new-types (set/difference (:types union-t)
                                    (if (union-type? removed-t)
                                      (:types removed-t)
                                      #{removed-t}))]
      (if (empty? new-types)
        ;; Return bottom type - this represents an unreachable path
        {:type :bottom}
        (union-type new-types)))
    (if (type-equal? union-t removed-t)
      {:type :bottom}  ;; Empty type if we removed the only type
      union-t)))       ;; No change if types don't match

(defn intersect-types [t1 t2]
  (cond
    ;; Handle any-type specially
    (any-type? t1) t2
    (any-type? t2) t1

    ;; Handle bottom type
    (= (:type t1) :bottom) t1
    (= (:type t2) :bottom) t2

    ;; If both are unions, intersect their type sets
    (and (union-type? t1) (union-type? t2))
    (let [common-types (set/intersection (:types t1) (:types t2))]
      (if (empty? common-types)
        {:type :bottom}
        (union-type common-types)))

    ;; If one is a union, filter to only types that are subtypes of the other
    (union-type? t1)
    (let [compatible-types (filter #(subtype? % t2) (:types t1))]
      (if (empty? compatible-types)
        {:type :bottom}
        (union-type compatible-types)))

    (union-type? t2)
    (let [compatible-types (filter #(subtype? % t1) (:types t2))]
      (if (empty? compatible-types)
        {:type :bottom}
        (union-type compatible-types)))

    ;; For simple types, if they're equal return one, otherwise bottom
    (type-equal? t1 t2) t1
    :else {:type :bottom}))

;; Predicate refinement table
(def predicate-refinements
  {'number? {:test-type int-type
             :refine-true (fn [var-type] (intersect-types var-type int-type))
             :refine-false (fn [var-type] (remove-type var-type int-type))}
   'string? {:test-type string-type
             :refine-true (fn [var-type] (intersect-types var-type string-type))
             :refine-false (fn [var-type] (remove-type var-type string-type))}
   'boolean? {:test-type bool-type
              :refine-true (fn [var-type] (intersect-types var-type bool-type))
              :refine-false (fn [var-type] (remove-type var-type bool-type))}})

;; Check if a symbol is a known predicate
(defn predicate-fn? [sym]
  (contains? predicate-refinements sym))

;; Macros for boolean operations
(def macros
  {'and (fn [x y] (list 'if x y false))
   'or  (fn [x y] (list 'if x true y))
   'not (fn [x]   (list 'if x false true))})

;; Simple macroexpander - does one level of expansion
(defn expand-1 [form]
  (if (and (seq? form) (symbol? (first form)))
    (let [macro-fn (get macros (first form))]
      (if macro-fn
        (apply macro-fn (rest form))
        form))
    form))

(defn expand-all [form]
  (let [expanded (expand-1 form)]
    (if (= expanded form)
      ;; No expansion occurred at this level, so recurse into sub-forms
      (if (seq? form)
        ;; Preserve the list structure by using map+list instead of just map
        (apply list (map expand-all form))
        form)
      ;; Expansion occurred, so recurse on the expanded form
      (expand-all expanded))))

;; Generic environment refinement using the predicate table

;; Refine environment for a type predicate
(defn refine-env-for-predicate [env var pred is-true?]
  (if-let [var-type (get env var)]
    (if-let [refinement (get predicate-refinements pred)]
      (let [refine-fn (if is-true?
                        (:refine-true refinement)
                        (:refine-false refinement))]
        (assoc env var (refine-fn var-type)))
      env)  ;; No refinement defined for this predicate
    env))  ;; Variable not found in environment

;; Extract variable and predicate from a type test
(defn extract-type-test [expr]
  (when (and (seq? expr)
             (= (count expr) 2)
             (predicate-fn? (first expr)))
    {:predicate (first expr)
     :var (second expr)}))

;; Type refinement for function calls
(defn get-arg-refinements [fn-type args]
  "Return a list of [arg-idx, required-type] pairs for function arguments"
  (when (function-type? fn-type)
    (let [param-type (:param-type fn-type)]
      (cond
        ;; Single argument function where arg is a symbol
        (and (= (count args) 1) (symbol? (first args)))
        [[0 param-type]]

        ;; Handle nested function applications like (< (string-length x) 5)
        (and (= (count args) 2)
             (seq? (first args))
             (symbol? (first (first args)))
             (= (first (first args)) 'string-length))
        (let [inner-arg (second (first args))]
          (when (symbol? inner-arg)
            [[0 string-type]]))  ;; The arg to string-length must be a string

        ;; Other multi-argument cases
        :else '()))))

;; Default environment with built-in predicates and string-length function
(defn default-env []
  {'number? (function-type any-type bool-type)
   'boolean? (function-type any-type bool-type)
   'string? (function-type any-type bool-type)
   'string-length (function-type string-type int-type)
   '< (function-type int-type bool-type)
   '> (function-type int-type bool-type)
   '+ (function-type int-type int-type)})

;; Core environment refinement logic for arbitrary conditions
(defn refine-env-by-condition [env condition]
  (let [expanded (expand-all condition)]
    (cond
      ;; Direct type predicate application
      (extract-type-test expanded)
      (let [{:keys [predicate var]} (extract-type-test expanded)]
        [(refine-env-for-predicate env var predicate true)
         (refine-env-for-predicate env var predicate false)])

      ;; Function application - use bidirectional type inference
      (and (seq? expanded) (not-empty expanded))
      (let [func (first expanded)
            args (rest expanded)]
        (if-let [fn-type (get env func)]
          (if-let [refinements (get-arg-refinements fn-type args)]
            ;; Apply refinements from function type constraints
            (let [refined-env (reduce (fn [e [arg-idx req-type]]
                                        (let [arg (nth args arg-idx)]
                                          (if (symbol? arg)
                                            (if-let [arg-type (get e arg)]
                                              (assoc e arg (intersect-types arg-type req-type))
                                              e)
                                            e)))
                                      env
                                      refinements)]
              ;; For successful application, type is refined in true branch
              ;; For false branch, we can't say much
              [refined-env env])
            [env env])
          [env env]))

      ;; Handle expanded if-expressions from macros
      (and (seq? expanded) (= (first expanded) 'if))
      (let [test (nth expanded 1)
            then-result (nth expanded 2)
            else-result (nth expanded 3 nil)
            [test-true-env test-false-env] (refine-env-by-condition env test)]

        (cond
          ;; Expanded OR: (if test true else-expr)
          (= then-result true)
          [test-true-env
           (first (refine-env-by-condition test-false-env else-result))]

          ;; Expanded AND: (if test else-expr false)
          (= else-result false)
          [(first (refine-env-by-condition test-true-env then-result))
           test-false-env]

          ;; Regular if
          :else
          [(first (refine-env-by-condition test-true-env then-result))
           (first (refine-env-by-condition test-false-env else-result))]))

      ;; Default - no refinement possible
      :else [env env])))

;; Define analyze-expr before it's used in test functions
(declare typecheck) ;; Forward declaration to handle mutual recursion

(defn analyze-expr [expr]
  (println "\nAnalyzing expression:" expr)
  (let [expanded (expand-all expr)]
    (println "Expanded:" expanded)
    (try
      (let [result-type (typecheck (default-env) expanded)]
        (println "Result type:" result-type)
        result-type)
      (catch Exception e
        (println "Type error:" (.getMessage e))
        (println "  Details:" (ex-data e))
        nil))))

;; Pre-refinement functions to analyze and apply type constraints before checking

(defn get-function-requirements
  "Extracts type requirements from a function application"
  [env expr]
  (when (and (seq? expr) (not-empty expr))
    (let [fn-name (first expr)
          args (rest expr)]
      (if-let [fn-type (get env fn-name)]
        (if (function-type? fn-type)
          ;; Handle direct function application (e.g., string-length x)
          (if (= (count args) 1)
            (when (symbol? (first args))
              {(first args) (:param-type fn-type)})
            {})
          {})
        ;; Check for nested function applications in arguments
        (apply merge (map #(get-function-requirements env %) args))))))

(defn analyze-expr-requirements
  "Recursively analyze an expression for type requirements"
  [env expr]
  (cond
    ;; Simple cases - literals, variables
    (or (integer? expr) (boolean? expr) (string? expr)) {}
    
    ;; Variable reference - no requirements
    (symbol? expr) {}
    
    ;; Let expression
    (and (seq? expr) (= (first expr) 'let))
    (let [bindings (second expr)
          body (nth expr 2)]
      (if (and (vector? bindings) (even? (count bindings)))
        (loop [remaining-bindings bindings
               req-env {}
               local-env env]
          (if (empty? remaining-bindings)
            (merge req-env (analyze-expr-requirements local-env body))
            (let [var-name (first remaining-bindings)
                  var-expr (second remaining-bindings)
                  var-reqs (analyze-expr-requirements local-env var-expr)]
              (recur (drop 2 remaining-bindings)
                     (merge req-env var-reqs)
                     (assoc local-env var-name (typecheck local-env var-expr))))))
        {}))
    
    ;; Union type - analyze each component
    (and (seq? expr) (= (first expr) 'union))
    (apply merge (map #(analyze-expr-requirements env %) (rest expr)))
    
    ;; If expression - analyze each part
    (and (seq? expr) (= (first expr) 'if))
    (let [condition (nth expr 1)
          then-expr (nth expr 2)
          else-expr (nth expr 3 nil)]
      (merge
        (analyze-expr-requirements env condition)
        (analyze-expr-requirements env then-expr)
        (if else-expr
          (analyze-expr-requirements env else-expr)
          {})))
    
    ;; Function application
    (and (seq? expr) (not-empty expr))
    (let [fn-requirements (get-function-requirements env expr)]
      ;; Also analyze arguments for nested requirements
      (apply merge fn-requirements 
             (map #(analyze-expr-requirements env %) (rest expr))))
    
    :else {}))

(defn apply-requirements
  "Apply type requirements to refine the environment"
  [env requirements]
  (reduce (fn [e [var req-type]]
            (if-let [var-type (get e var)]
              (assoc e var (intersect-types var-type req-type))
              e))
          env
          requirements))

;; Enhanced typechecker with pre-refinement pass
(defn typecheck 
  "Typechecks an expression with the given environment.
   Returns the type of the expression if successful, throws an error otherwise."
  [env expr]
  (let [requirements (analyze-expr-requirements env expr)
        refined-env (apply-requirements env requirements)]
    (cond
      ;; Integer literal
      (integer? expr) int-type
  
      ;; Boolean literal
      (boolean? expr) bool-type
  
      ;; String literal
      (string? expr) string-type
  
      ;; Variable reference
      (symbol? expr) (if-let [t (get refined-env expr)]
                       t
                       (throw (ex-info (str "Unbound variable: " expr)
                                       {:expr expr :env refined-env})))
  
      ;; Let expression: (let [x e1] e2)
      (and (seq? expr) (= (first expr) 'let))
      (let [bindings (second expr)
            body (nth expr 2)]
        (if (and (vector? bindings) (even? (count bindings)))
          (loop [remaining-bindings bindings
                 new-env refined-env]
            (if (empty? remaining-bindings)
              (typecheck new-env body)
              (let [var-name (first remaining-bindings)
                    var-expr (second remaining-bindings)
                    var-type (typecheck refined-env var-expr)]
                (recur (drop 2 remaining-bindings)
                       (assoc new-env var-name var-type)))))
          (throw (ex-info "Invalid let bindings" {:expr expr}))))
  
      ;; Union type annotation: (union t1 t2 ...)
      (and (seq? expr) (= (first expr) 'union))
      (let [types (map #(typecheck refined-env %) (rest expr))]
        (union-type types))
  
      ;; If expression with occurrence typing: (if condition then-expr else-expr)
      (and (seq? expr) (= (first expr) 'if))
      (let [condition (nth expr 1)
            then-expr (nth expr 2)
            else-expr (nth expr 3 nil)  ;; Make else-expr optional
            condition-type (typecheck refined-env condition)
            [then-env else-env] (refine-env-by-condition refined-env condition)]
        (if (bool-type? condition-type)
          (let [then-type (typecheck then-env then-expr)
                else-type (if else-expr
                            (typecheck else-env else-expr)
                            nil-type)]  ;; Use nil-type if no else expr
            (union-type [then-type else-type]))
          (throw (ex-info "Condition must be a boolean"
                          {:expr condition :type condition-type}))))
      
      ;; Function application: (f arg1 arg2 ...)
      (and (seq? expr) (not-empty expr))
      (let [fn-expr (first expr)
            args (rest expr)]
        (cond
          ;; Handle built-in operators that accept two arguments
          (contains? #{'< '> '+} fn-expr)
          (if (= (count args) 2)
            (let [arg1-type (typecheck refined-env (first args))
                  arg2-type (typecheck refined-env (second args))]
              ;; Return appropriate return type based on the operator
              (case fn-expr
                < bool-type
                > bool-type
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
          (let [fn-type (typecheck refined-env fn-expr)]
            (if (function-type? fn-type)
              (if (= (count args) 1)
                (let [arg-expr (first args)
                      arg-type (typecheck refined-env arg-expr)]
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
                            {:expr expr})))))

;; Test examples for bidirectional function type inference
(defn test-bidirectional-inference []
  (println "\n=== BIDIRECTIONAL TYPE INFERENCE TESTS ===\n")

  ;; Test 1: Basic function application in a conditional
  (analyze-expr '(let [x (union 42 "hello")]
                  (if (< (string-length x) 5)  ;; This should refine x to string in the then branch
                    "short string"
                    "something else")))

  ;; Test 2: Function with complex conditional
  (analyze-expr '(let [x (union 42 "hello")]
                  (if (> 5 (string-length x))  ;; Order shouldn't matter
                    "short string"
                    "something else")))

  ;; Test 3: Using (if (string-length x) ...) as a truthy test
  (analyze-expr '(let [x (union 42 "hello")]
                  (if (string-length x)  ;; This should refine x to string in the then branch
                    "has a length"
                    "not a string or empty string")))

  ;; Test 4: Multiple function applications in condition
  (analyze-expr '(let [x (union 42 "hello")
                       y (union 42 "world")]
                  (if (< (string-length x) (string-length y))  ;; Both x and y should be refined to string
                    "x is shorter than y"
                    "x is not shorter than y")))

  (println "\nBidirectional inference tests completed."))

;; Add this to the main test function
(defn test-occurrence-typing []
  (println "\n=== OCCURRENCE TYPING TESTS ===\n")

  ;; Test 1: Basic type predicates
  (analyze-expr '(let [x (union 42 "hello")]
                  (if (string? x)
                    (string-length x)
                    0)))

  ;; Test 2: Compound boolean expressions with AND
  (analyze-expr '(let [x (union 42 "hello" true)]
                  (if (and (string? x) (< (string-length x) 5))
                    "short string"
                    "something else")))

  ;; Test 3: Compound boolean expressions with OR
  (analyze-expr '(let [x (union 42 "hello" true)]
                  (if (or (number? x) (string? x))
                    "number or string"
                    "must be boolean")))

  ;; Test 4: Complex nested expressions
  (analyze-expr '(let [x (union 42 "hello" true)]
                  (if (or (number? x)
                          (and (string? x) (< (string-length x) 5)))
                    "valid value"
                    "other")))

  ;; Test 5: Refinement in nested code blocks
  (analyze-expr '(let [x (union 42 "hello" true)]
                  (if (string? x)
                    (string-length x)  ;; x is string here
                    (if (number? x)
                      (+ x 10)         ;; x is number here
                      "must be boolean"))))  ;; x is boolean here

  ;; Test 6: Type error when an inadmissible operation is attempted
  (analyze-expr '(let [x (union 42 "hello")]
                  (string-length x)))  ;; Should fail - x might be an int

  ;; Test 7: Logical negation
  (analyze-expr '(let [x (union 42 "hello" true)]
                  (if (not (string? x))
                    "not a string"
                    (string-length x))))  ;; x is string here

  ;; Test 8: Nested refinements with multiple predicates
  (analyze-expr '(let [x (union 42 "hello" true)]
                  (if (string? x)
                    (if (< (string-length x) 10)
                      "short string"  ;; x is string with length < 10
                      "long string")  ;; x is string with length >= 10
                    "not a string"))) ;; x is number or boolean

  ;; Add the bidirectional inference tests
  (test-bidirectional-inference)

  (println "\nOccurrence typing tests completed."))

;; Run the tests
(test-occurrence-typing)
