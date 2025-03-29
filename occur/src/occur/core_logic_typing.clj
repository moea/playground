(ns occur.core-logic-typing
  (:require [clojure.set :as set]))

;;; ---- Type System Core ----

;; Basic primitive types
(def int-type :int)
(def string-type :string)
(def bool-type :bool)
(def any-type :any)
(def bottom-type :bottom)

;; ----- Updated Type Representation -----
;; Types are represented using:
;; - Keywords for primitive types (:int, :string, :bool, :any, :bottom)
;; - Sets for union types #{:int :string}
;; - Maps with :type :function for function types

;; Type constructors and predicates
(defn union-type 
  "Create a union type from a collection of types.
   Can be called with either a collection or multiple arguments."
  [types & more-types]
  (let [all-types (if (and (coll? types) (empty? more-types))
                    types  ;; Called with a single collection
                    (cons types more-types))  ;; Called with multiple args
        flattened (reduce (fn [acc t]
                            (if (set? t)
                              (set/union acc t)
                              (conj acc t)))
                          #{}
                          all-types)]
    (cond
      (empty? flattened) bottom-type
      (= (count flattened) 1) (first flattened)
      :else flattened)))

(defn function-type 
  "Create a function type with specified parameter types and return type.
   Supports fixed arity functions with multiple parameters."
  ([param-types return-type]
   {:type :function 
    :param-types (if (vector? param-types) param-types [param-types])
    :return-type return-type})
  ([param-type1 param-type2 & more-types]
   (let [return-type (last more-types)
         param-types (vec (concat [param-type1 param-type2] 
                                 (butlast more-types)))]
     {:type :function
      :param-types param-types
      :return-type return-type})))

;; Type predicates
(defn primitive-type? [t] (keyword? t))
(defn union-type? [t] (set? t))
(defn function-type? [t] (and (map? t) (= (:type t) :function)))

;; Helper to get types from a union
(defn union-types [t]
  (if (set? t) t #{t}))

;; Subtyping and type compatibility functions
(defn subtype? [sub-type super-type]
  (cond
    ;; Any type is a supertype of all types
    (= super-type any-type) true

    ;; Bottom type is a subtype of all types
    (= sub-type bottom-type) true

    ;; Same types
    (= sub-type super-type) true

    ;; Union type supertype - sub-type must be a subset of super-type
    (set? super-type)
    (if (set? sub-type)
      (every? (fn [t] (some #(subtype? t %) super-type)) sub-type)
      (contains? super-type sub-type))

    ;; Union type subtype - all elements must be subtypes of super-type
    (set? sub-type)
    (every? (fn [t] (subtype? t super-type)) sub-type)

    ;; Function subtyping - contravariant in parameter types, covariant in return type
    (and (function-type? sub-type) (function-type? super-type))
    (let [sub-params (:param-types sub-type)
          super-params (:param-types super-type)]
      (and 
       ;; Same number of parameters
       (= (count sub-params) (count super-params))
       ;; Contravariant in parameter types
       (every? identity (map subtype? super-params sub-params))
       ;; Covariant in return type
       (subtype? (:return-type sub-type) (:return-type super-type))))

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
    (set? t1)
    (let [intersected (filter (fn [t] (not= (intersect-types t t2) bottom-type))
                              t1)]
      (if (empty? intersected)
        bottom-type
        (union-type intersected)))

    (set? t2)
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
    (set? t1)
    (let [diff-types (filter (fn [t] (not= (intersect-types t t2) t))
                             t1)]
      (if (empty? diff-types)
        bottom-type
        (union-type diff-types)))

    ;; Difference with a union type on right
    (set? t2)
    (let [remaining-type (reduce (fn [curr-type remove-type]
                                   (type-difference curr-type remove-type))
                                 t1
                                 t2)]
      remaining-type)

    ;; Simple types that don't match - no change
    :else t1))

(defn compatible-with-bool? [t]
  (or (= t bool-type)
      (and (set? t) (contains? t bool-type))))

;;; ---- Constraint System ----

;; ----- #1: Streamlined Boolean Constraint Handling -----
;; Using plain data structures instead of records for constraints

;; Define type predicates
(def predicate-type-map
  {'number? int-type
   'string? string-type
   'boolean? bool-type})

;; Initialize environment with primitives
(defn init-env []
  (merge
    {;; Fixed arity functions
     'string-length (function-type [string-type] int-type)
     
     ;; Operators that support multiple arguments
     ;; Note: For operators like <, >, =, +, we define them with their minimal arity (2 params)
     ;; in the environment, but the typecheck function has special handling to allow them
     ;; to accept any number of arguments (>= 2) at application sites
     '< (function-type [int-type int-type] bool-type)  ;; < operator (2+ args)
     '> (function-type [int-type int-type] bool-type)  ;; > operator (2+ args)
     '= (function-type [any-type any-type] bool-type)  ;; = operator (2+ args)
     '+ (function-type [int-type int-type] int-type)   ;; + operator (2+ args)
     
     ;; Boolean operators
     'and (function-type [bool-type bool-type] bool-type)
     'or (function-type [bool-type bool-type] bool-type)
     'not (function-type [bool-type] bool-type)
    }
    
    ;; Add predicates to environment as functions - each takes a single any-type param
    (reduce-kv (fn [env pred-name _]
                 (assoc env
                        pred-name
                        (function-type [any-type] bool-type)))
               {}
               predicate-type-map)))

;;; ----- #3: Simplified Formula Extraction and Application -----
;;; ----- #1: Simplified Boolean Constraints -----

;; Boolean formula constructors
(defn type-constraint [var type] 
  {:constraint :type, :var var, :type type})

(defn conjunction [clauses] 
  (let [flattened (mapcat (fn [c] 
                            (if (and (map? c) (= (:constraint c) :conjunction))
                              (:clauses c) 
                              [c])) 
                          clauses)
        filtered (filter #(not= % true) flattened)]
    (cond
      (some #(= % false) filtered) false
      (empty? filtered) true
      (= (count filtered) 1) (first filtered)
      :else {:constraint :conjunction, :clauses filtered})))

(defn disjunction [clauses]
  (let [flattened (mapcat (fn [c] 
                            (if (and (map? c) (= (:constraint c) :disjunction))
                              (:clauses c) 
                              [c])) 
                          clauses)
        filtered (filter #(not= % false) flattened)]
    (cond
      (some #(= % true) filtered) true
      (empty? filtered) false
      (= (count filtered) 1) (first filtered)
      :else {:constraint :disjunction, :clauses filtered})))

(defn negation [formula]
  (cond
    (= formula true) false
    (= formula false) true
    (and (map? formula) (= (:constraint formula) :negation))
    (:formula formula)  ;; Double negation
    :else {:constraint :negation, :formula formula}))

;; Formula type predicates
(defn type-constraint? [formula] 
  (and (map? formula) (= (:constraint formula) :type)))

(defn conjunction? [formula] 
  (and (map? formula) (= (:constraint formula) :conjunction)))

(defn disjunction? [formula] 
  (and (map? formula) (= (:constraint formula) :disjunction)))

(defn negation? [formula] 
  (and (map? formula) (= (:constraint formula) :negation)))

;; Convert formula to negation normal form
(defn to-nnf [formula]
  (cond
    ;; Constants are already in NNF
    (or (= formula true) (= formula false)) formula
    
    ;; Atomic constraints are already in NNF
    (type-constraint? formula) formula
    
    ;; Negations need to be pushed inward
    (negation? formula)
    (let [inner (:formula formula)]
      (cond
        ;; Negation of constants
        (= inner true) false
        (= inner false) true
        
        ;; Negation of atomic constraint
        (type-constraint? inner)
        formula  ;; Keep as is, represents negated predicate
        
        ;; De Morgan's laws: push negation inward
        (conjunction? inner)
        (disjunction (map #(to-nnf (negation %)) (:clauses inner)))
        
        (disjunction? inner)
        (conjunction (map #(to-nnf (negation %)) (:clauses inner)))
        
        ;; Double negation
        (negation? inner)
        (to-nnf (:formula inner))
        
        ;; Default case - just wrap in negation
        :else formula))
    
    ;; Process compound formulas recursively
    (conjunction? formula)
    (conjunction (map to-nnf (:clauses formula)))
    
    (disjunction? formula)
    (disjunction (map to-nnf (:clauses formula)))
    
    :else formula))

;; ----- #3: Simplified Constraint Extraction and Application -----

;; Extract a predicate from an expression
(defn extract-predicate [expr]
  (cond
    ;; Standard type predicates (e.g., number? var)
    (and (seq? expr) (symbol? (first expr)))
    (when-let [type (get predicate-type-map (first expr))]
      (when (= (count expr) 2)
        (type-constraint (second expr) type)))
    
    ;; Handle equality comparisons with literals
    (and (seq? expr) (= (first expr) '=) (>= (count (rest expr)) 2))
    (let [args (rest expr)]
      (cond
        ;; Check for variable comparison with a literal
        (and (symbol? (first args)) (not (symbol? (second args))))
        (let [var (first args)
              literal (second args)]
          ;; Create constraint based on literal type
          (cond
            (integer? literal) (type-constraint var :int)
            (string? literal) (type-constraint var :string)
            (boolean? literal) (type-constraint var :bool)
            :else nil))
            
        ;; Check for literal comparison with a variable
        (and (not (symbol? (first args))) (symbol? (second args)))
        (let [literal (first args)
              var (second args)]
          ;; Create constraint based on literal type
          (cond
            (integer? literal) (type-constraint var :int)
            (string? literal) (type-constraint var :string)
            (boolean? literal) (type-constraint var :bool)
            :else nil))
            
        :else nil))
    
    ;; Handle comparison operators like <, >
    (and (seq? expr) (contains? #{'< '>} (first expr)) (>= (count (rest expr)) 2))
    (let [op (first expr)
          args (rest expr)]
      ;; For < and >, all arguments must be numbers
      (when (some symbol? args)
        ;; Create a conjunction of constraints for all variables
        (let [var-constraints 
              (for [arg args :when (symbol? arg)]
                (type-constraint arg :int))]
          (if (= (count var-constraints) 1)
            (first var-constraints)
            (conjunction var-constraints)))))
    
    :else nil))

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
              (negation inner))

        and (let [inner-formulas (keep extract-formula args)]
              (if (seq inner-formulas)
                (conjunction inner-formulas)
                nil))

        or (let [inner-formulas (keep extract-formula args)]
             (if (seq inner-formulas)
               (disjunction inner-formulas)
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
                (conjunction inner-formulas)))))))

    ;; Default
    :else nil))

;; Refine environment with a constraint
(defn refine-env [env var constraint positive?]
  (if-let [curr-type (get env var)]
    (let [target-type (case constraint
                        :int int-type
                        :string string-type
                        :bool bool-type
                        constraint)
          refined-type (if positive?
                         (intersect-types curr-type target-type)
                         (type-difference curr-type target-type))]
      (if (= refined-type bottom-type)
        env  ;; Constraint cannot be satisfied
        (assoc env var refined-type)))
    env))

;; Apply a single type constraint
(defn apply-constraint [env constraint positive?]
  (if (type-constraint? constraint)
    (refine-env env (:var constraint) (:type constraint) positive?)
    env))

;; Helper for handling disjunctions - merge environments by taking union of types
(defn merge-environments [base-env & envs]
  (if (empty? envs)
    base-env
    (let [all-vars (set (mapcat #(keys (select-keys % (keys base-env))) envs))
          ;; For each variable, take the union of its type across all branches
          merged-env (reduce (fn [result var]
                               (let [branch-types (keep #(get % var) envs)]
                                 (if (seq branch-types)
                                   (assoc result var (apply union-type branch-types))
                                   result)))
                             base-env
                             all-vars)]
      merged-env)))

;; Apply a boolean formula to refine the environment
(defn apply-formula [env formula positive?]
  (cond
    ;; Boolean constants - no-op
    (or (= formula true) (= formula false)) env

    ;; Simple type constraint
    (type-constraint? formula)
    (apply-constraint env formula positive?)

    ;; Negation - apply inner formula with flipped positive flag
    (negation? formula)
    (apply-formula env (:formula formula) (not positive?))

    ;; Conjunction - apply each clause in sequence
    (conjunction? formula)
    (reduce (fn [e clause]
              (apply-formula e clause positive?))
            env
            (:clauses formula))

    ;; Disjunction - apply each clause and merge environments
    (disjunction? formula)
    (let [refined-envs (map #(apply-formula env % positive?)
                           (:clauses formula))]
      (reduce merge-environments env refined-envs))

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
        formula (when raw-formula (to-nnf raw-formula))

        ;; Refine environment for both branches
        then-env (if formula
                   (apply-formula env formula true)
                   env)
        else-env (if formula
                   (apply-formula env (negation formula) true)
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

;; Shared function for handling operators
(defn check-operator [env op args min-args arg-pred result-type error-msg]
  (when (< (count args) min-args)
    (throw (ex-info (str op " requires at least " min-args " arguments")
                   {:expr (cons op args)})))
  (let [arg-types (mapv #(typecheck env %) args)]
    (doseq [arg-type arg-types]
      (when-not (arg-pred arg-type)
        (throw (ex-info error-msg
                       {:arg-types arg-types}))))
    result-type))

;; Define multimethod for typechecking different expression types
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
(defmethod typecheck-expr :keyword [_ expr] expr) ;; Direct type keyword

;; Handle variable references
(defmethod typecheck-expr :symbol [env expr]
  (if-let [t (get env expr)]
    t
    (throw (ex-info (str "Unbound variable: " expr)
                   {:expr expr :env env}))))

;; Handle let expressions: (let [x e1 y e2...] body)
(defmethod typecheck-expr 'let [env [_ bindings body]]
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
    (throw (ex-info "Invalid let bindings" {:expr ['let bindings body]}))))

;; Handle union type expressions: (union t1 t2...)
(defmethod typecheck-expr 'union [env [_ & types]]
  (let [types (map #(typecheck env %) types)]
    (union-type types)))

;; Handle if expressions with boolean formula constraint solving
(defmethod typecheck-expr 'if [env [_ condition then else]]
  (typecheck-if-enhanced env condition then else))

;; Handle boolean operators: and, or, not
(defmethod typecheck-expr 'and [env [_ & args]]
  (doseq [arg args]
    (let [arg-type (typecheck env arg)]
      (when-not (compatible-with-bool? arg-type)
        (throw (ex-info "Arguments to 'and' must be boolean compatible"
                       {:expr arg :type arg-type})))))
  bool-type)

(defmethod typecheck-expr 'or [env [_ & args]]
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

;; Handle special operators: <, >, =, +
(defmethod typecheck-expr '< [env [op & args]]
  (check-operator env op args 2 
                 #(subtype? % int-type) 
                 bool-type
                 (str "Arguments to " op " must be numbers")))

(defmethod typecheck-expr '> [env [op & args]]
  (check-operator env op args 2 
                 #(subtype? % int-type) 
                 bool-type
                 (str "Arguments to " op " must be numbers")))

(defmethod typecheck-expr '= [env [op & args]]
  (check-operator env op args 2 
                 (fn [_] true) ;; = accepts any type
                 bool-type
                 "Invalid argument types for ="))

(defmethod typecheck-expr '+ [env [op & args]]
  (check-operator env op args 2 
                 #(subtype? % int-type) 
                 int-type
                 "Arguments to + must be numbers"))

;; Handle general function application
(defmethod typecheck-expr :default [env [fn-expr & args]]
  (let [fn-type (typecheck env fn-expr)]
    (if (function-type? fn-type)
      (let [param-types (:param-types fn-type)]
        (cond
          ;; No arguments, but function expects parameters
          (and (empty? args) (not-empty param-types))
          (throw (ex-info "Function requires arguments but none provided"
                        {:fn-type fn-type}))
          
          ;; No arguments, function expects no parameters
          (and (empty? args) (empty? param-types))
          (:return-type fn-type)
          
          ;; Check if argument count matches parameter count
          (not= (count args) (count param-types))
          (throw (ex-info (str "Function expects " (count param-types) 
                             " arguments but got " (count args))
                        {:fn-type fn-type
                         :args-count (count args)}))
          
          ;; Check each argument against corresponding parameter type
          :else
          (do
            (doseq [[arg param-type] (map vector args param-types)]
              (let [arg-type (typecheck env arg)]
                (when-not (subtype? arg-type param-type)
                  (throw (ex-info "Argument type doesn't match parameter type"
                                {:fn-type fn-type
                                 :arg-type arg-type
                                 :param-type param-type})))))
            (:return-type fn-type))))
      (throw (ex-info "Applying a non-function"
                    {:expr (cons fn-expr args)
                     :fn-type fn-type})))))

;; Handle unknown expression types
(defmethod typecheck-expr :unknown [_ expr]
  (throw (ex-info (str "Unsupported expression: " expr)
                 {:expr expr})))

(defmethod typecheck-expr :empty-list [_ _]
  (throw (ex-info "Cannot typecheck an empty list" 
                 {:expr '()})))

;; Simplified typecheck function that delegates to the multimethod
(defn typecheck [env expr]
  (typecheck-expr env expr))

;;; ---- Testing ----

(defn -main [& args]
  (println "Simplified Occurrence Typing System")
  (println "To run the tests, use: lein test occur.core-logic-typing-test"))
