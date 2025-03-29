(ns occur.toy-typing
  (:require [clojure.set :as set]))

;;;; Core Type Definitions ;;;;

;; Primitive Types
(def int-type :int)
(def bool-type :bool)
(def string-type :string)
(def any-type :any)  ;; Top type - all values have this type
(def nil-type {:type :nil})  ;; Nil type for optional values
(def bottom-type {:type :bottom})  ;; Bottom type - no values can have this type

;; Type Predicates
(defn int-type? [t] (= t int-type))
(defn bool-type? [t] (= t bool-type))
(defn string-type? [t] (= t string-type))
(defn any-type? [t] (= t any-type))
(defn nil-type? [t] (= t nil-type))
(defn bottom-type? [t] (= t bottom-type))
(defn union-type? [t] (and (map? t) (= (:type t) :union)))
(defn function-type? [t] (and (map? t) (= (:type t) :function)))

;; Type Constructors
(defn union-type [types]
  (let [types-set (set types)]
    (cond
      (empty? types-set) bottom-type
      (= (count types-set) 1) (first types-set)
      :else {:type :union
             :types types-set})))

(defn function-type [param-type return-type]
  {:type :function
   :param-type param-type
   :return-type return-type})

;; Forward declarations for mutually recursive functions
(declare subtype? type-equal? intersect-types remove-type typecheck)

;; Type Operations
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
    (bottom-type? t1) true  ;; Bottom is a subtype of everything
    (any-type? t2) true     ;; Everything is a subtype of Any
    (type-equal? t1 t2) true
    
    (union-type? t2) (if (union-type? t1)
                       (every? (fn [t] (some #(subtype? t %) (:types t2))) (:types t1))
                       (some #(subtype? t1 %) (:types t2)))
    
    (union-type? t1) (every? #(subtype? % t2) (:types t1))
    
    (and (function-type? t1) (function-type? t2))
    (and (subtype? (:param-type t2) (:param-type t1))  ; Contravariant in param type
         (subtype? (:return-type t1) (:return-type t2))) ; Covariant in return type
    
    :else false))

(defn intersect-types [t1 t2]
  (cond
    ;; Handle special types
    (bottom-type? t1) t1
    (bottom-type? t2) t2
    (any-type? t1) t2
    (any-type? t2) t1
    
    ;; If both are unions, intersect their type sets
    (and (union-type? t1) (union-type? t2))
    (let [common-types (set/intersection (:types t1) (:types t2))]
      (if (empty? common-types)
        bottom-type
        (union-type common-types)))
    
    ;; If one is a union, filter to only types that are subtypes of the other
    (union-type? t1)
    (let [compatible-types (filter #(subtype? % t2) (:types t1))]
      (if (empty? compatible-types)
        bottom-type
        (union-type compatible-types)))
    
    (union-type? t2)
    (let [compatible-types (filter #(subtype? % t1) (:types t2))]
      (if (empty? compatible-types)
        bottom-type
        (union-type compatible-types)))
    
    ;; For simple types, if they're equal return one, otherwise bottom
    (type-equal? t1 t2) t1
    :else bottom-type))

(defn remove-type [union-t removed-t]
  (if (union-type? union-t)
    (let [new-types (set/difference (:types union-t) 
                                    (if (union-type? removed-t)
                                      (:types removed-t)
                                      #{removed-t}))]
      (if (empty? new-types)
        bottom-type
        (union-type new-types)))
    (if (type-equal? union-t removed-t)
      bottom-type
      union-t)))

(defn compatible-with-bool? [t]
  (cond 
    (bool-type? t) true
    (int-type? t) true    ;; Non-zero is true
    (string-type? t) true ;; Non-empty is true
    (union-type? t) (or (contains? (:types t) bool-type)
                        (some compatible-with-bool? (:types t)))
    :else false))

;;;; Constraint System ;;;;

;; Maps predicate names to their corresponding types
(def predicate-type-map
  {'number? int-type
   'boolean? bool-type
   'string? string-type})

;; Constraint Protocol
(defprotocol TypeConstraint
  (apply-constraint [this env is-positive])
  (describe [this]))

;; Variable Type Constraint
(defrecord TypePredicate [var type]
  TypeConstraint
  (apply-constraint [this env is-positive]
    (if is-positive
      (if-let [var-type (get env (:var this))]
        (assoc env (:var this) (intersect-types var-type (:type this)))
        env)
      (if-let [var-type (get env (:var this))]
        (assoc env (:var this) (remove-type var-type (:type this)))
        env)))
  
  (describe [this]
    (if (keyword? (:type this))
      (str (:var this) " is " (name (:type this)))
      (str (:var this) " is " (:type this)))))

;; Extract constraints from an expression
(defn extract-predicate-constraint [expr]
  "Extract type constraint from a predicate application"
  (when (and (seq? expr) (= (count expr) 2) (symbol? (first expr)))
    (when-let [type (get predicate-type-map (first expr))]
      (when (symbol? (second expr))
        (->TypePredicate (second expr) type)))))

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

;;;; Type Requirements Analysis ;;;;

(defn extract-constraints [expr]
  "Extract all type constraints from an expression"
  (cond
    ;; Literal values - no constraints
    (or (integer? expr) (string? expr) (boolean? expr))
    []
    
    ;; Variable reference - no constraints
    (symbol? expr)
    []
    
    ;; Type predicate application
    :else
    (if-let [pred-constraint (extract-predicate-constraint expr)]
      [pred-constraint]
      (if (seq? expr)
        (case (first expr)
          ;; If expression - extract constraints from condition
          if (extract-constraints (second expr))
          
          ;; For other function applications, extract from arguments
          (mapcat extract-constraints (rest expr)))
        []))))

;; Control Flow Analysis
(defprotocol ControlFlowAnalysis
  (analyze-branches [this env])
  (result-type [this env]))

(defrecord IfBranch [condition then-expr else-expr]
  ControlFlowAnalysis
  (analyze-branches [this env]
    (let [constraints (extract-constraints (:condition this))
          then-env (reduce #(apply-constraint %2 %1 true) env constraints)
          else-env (reduce #(apply-constraint %2 %1 false) env constraints)]
      [{:branch-name "then" :env then-env :expr (:then-expr this)}
       {:branch-name "else" :env else-env :expr (:else-expr this)}]))
  
  (result-type [this env]
    (let [branches (analyze-branches this env)
          then-type (typecheck (:env (first branches)) (:expr (first branches)))
          else-type (typecheck (:env (second branches)) (:expr (second branches)))]
      (union-type [then-type else-type]))))

;; Default environment with built-in predicates and functions
(defn default-env []
  {'number? (function-type any-type bool-type)
   'boolean? (function-type any-type bool-type)
   'string? (function-type any-type bool-type)
   'string-length (function-type string-type int-type)
   '< (function-type int-type bool-type)
   '> (function-type int-type bool-type)
   '+ (function-type int-type int-type)})

;; Core typechecking function with generalized constraint and flow analysis
(declare typecheck) ;; Forward declaration for mutual recursion

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

    ;; If expression with generalized control flow analysis
    (and (seq? expr) (= (first expr) 'if))
    (let [condition (nth expr 1)
          then-expr (nth expr 2)
          else-expr (nth expr 3 nil)
          condition-type (typecheck env condition)
          if-branch (->IfBranch condition then-expr else-expr)]
      (if (compatible-with-bool? condition-type)
        (result-type if-branch env)
        (throw (ex-info "Condition must be a boolean-compatible type"
                        {:expr condition :type condition-type}))))
    
    ;; Function application: (f arg1 arg2 ...)
    (and (seq? expr) (not-empty expr))
    (let [fn-expr (first expr)
          args (rest expr)]
      (cond
        ;; Handle built-in operators that accept two arguments
        (contains? #{'< '> '+} fn-expr)
        (if (= (count args) 2)
          (let [arg1-type (typecheck env (first args))
                arg2-type (typecheck env (second args))]
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

;;;; Testing and Analysis ;;;;

(defn analyze-expr [expr]
  (println "\nAnalyzing expression:" expr)
  (let [expanded (expand-all expr)]
    (println "Expanded:" expanded)
    (try
      (let [constraints (extract-constraints expanded)]
        (when (not-empty constraints)
          (println "Constraints:" (mapv describe constraints)))
        (let [result-type (typecheck (default-env) expanded)]
          (println "Result type:" result-type)
          result-type))
      (catch Exception e
        (println "Type error:" (.getMessage e))
        (println "  Details:" (ex-data e))
        nil))))

;; Test examples
(defn test-occurrence-typing []
  (println "\n=== GENERALIZED OCCURRENCE TYPING TESTS ===\n")
  
  ;; Basic type predicate
  (analyze-expr '(let [x (union 42 "hello")]
                   (if (string? x)
                     (string-length x)
                     0)))
  
  ;; Compound expressions
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (or (number? x) (string? x))
                     "number or string"
                     "boolean")))
  
  ;; Nested refinements
  (analyze-expr '(let [x (union 42 "hello" true)]
                   (if (string? x)
                     (string-length x)
                     (if (number? x)
                       (+ x 10)
                       "must be boolean"))))
  
  (println "\nTests completed."))

;; Run the tests
(test-occurrence-typing)
