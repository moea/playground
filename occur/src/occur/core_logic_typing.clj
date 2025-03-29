(ns occur.core-logic-typing
  (:require [clojure.core.logic :as l]
            [clojure.set :as set]
            [occur.boolean-constraints :as bc])
  (:import [occur.boolean_constraints TypeConstraint Negation Conjunction Disjunction]))

;;; ---- Type System Core ----

;; Basic primitive types
(def int-type :int)
(def string-type :string)
(def bool-type :bool)
(def any-type :any)
(def bottom-type :bottom)

;; Type constructors and predicates
(defn union-type 
  "Create a union type from a collection of types.
   Can be called with either a collection or multiple arguments."
  [types & more-types]
  (let [all-types (if (and (coll? types) (empty? more-types))
                    types  ;; Called with a single collection
                    (cons types more-types))  ;; Called with multiple args
        flattened (reduce (fn [acc t]
                            (if (and (map? t) (= (:type t) :union))
                              (set/union acc (:types t))
                              (conj acc t)))
                          #{}
                          all-types)]
    (cond
      (empty? flattened) bottom-type
      (= (count flattened) 1) (first flattened)
      :else {:type :union, :types flattened})))

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

;;; ---- Boolean Formula Adaptation ----

;; Initialize the boolean constraint solver with our type system functions
(def boolean-constraint-solver
  (bc/create-boolean-constraint-solver subtype? intersect-types type-difference union-type))

;; Helper functions to adapt between our typesystem and boolean_constraints.clj

;; Check formula type
(defn type-predicate? [formula]
  (instance? TypeConstraint formula))

(defn negation? [formula]
  (instance? Negation formula))

(defn conjunction? [formula]
  (instance? Conjunction formula))

(defn disjunction? [formula]
  (instance? Disjunction formula))

;; Get components
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
  (cond
    ;; Standard type predicates (e.g., number? var)
    (and (seq? expr) (symbol? (first expr)))
    (when-let [type (get predicate-type-map (first expr))]
      (when (= (count expr) 2)
        (bc/make-type-constraint (second expr) type)))
    
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
            (integer? literal) (bc/make-type-constraint var :int)
            (string? literal) (bc/make-type-constraint var :string)
            (boolean? literal) (bc/make-type-constraint var :bool)
            :else nil))
            
        ;; Check for literal comparison with a variable
        (and (not (symbol? (first args))) (symbol? (second args)))
        (let [literal (first args)
              var (second args)]
          ;; Create constraint based on literal type
          (cond
            (integer? literal) (bc/make-type-constraint var :int)
            (string? literal) (bc/make-type-constraint var :string)
            (boolean? literal) (bc/make-type-constraint var :bool)
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
                (bc/make-type-constraint arg :int))]
          (if (= (count var-constraints) 1)
            (first var-constraints)
            (bc/make-conjunction var-constraints)))))
    
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
    (let [;; Map the constraint type (:string, :int, :bool) to our type system (string-type, int-type, bool-type)
          target-type (case type
                        :int int-type
                        :string string-type
                        :bool bool-type
                        type)]
      
      ;; Handle it differently based on what's in the set
      (if (and (map? curr-type) (= (:type curr-type) :union))
        (if positive?
          ;; Positive constraint - keep only matching types
          (let [types (:types curr-type)
                result-types (case target-type
                              :int    (filter #(= % int-type) types)
                              :string (filter #(= % string-type) types)
                              :bool   (filter #(= % bool-type) types)
                              ;; Default
                              (filter #(= % target-type) types))]
            (if (empty? result-types)
              env
              (let [new-type (union-type result-types)]
                (assoc env var new-type))))
          
          ;; Negative constraint - remove matching types
          (let [types (:types curr-type)
                result-types (case target-type
                               :int    (remove #(= % int-type) types)
                               :string (remove #(= % string-type) types)
                               :bool   (remove #(= % bool-type) types)
                               ;; Default
                               (remove #(= % target-type) types))]
            (if (empty? result-types) 
              env
              (let [new-type (union-type result-types)]
                (assoc env var new-type)))))
        
        ;; Not a union type, use standard intersect/difference
        (let [refined-type (if positive?
                            (intersect-types curr-type target-type)
                            (type-difference curr-type target-type))]
          (if (= refined-type bottom-type)
            ;; Constraint cannot be satisfied
            env
            (assoc env var refined-type)))))
    ;; Variable not in environment
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

;; Apply boolean formula to refine environment
(defn apply-formula [env formula positive?]
  (cond
    ;; Boolean constants - no-op
    (or (= formula true) (= formula false)) env

    ;; Single predicate
    (type-predicate? formula)
    (apply-predicate env positive? (get-predicate-var formula) (get-predicate-type formula))

    ;; Negated predicate
    (and (negation? formula) (type-predicate? (get-negation-formula formula)))
    (let [pred (get-negation-formula formula)]
      (apply-predicate env (not positive?) (get-predicate-var pred) (get-predicate-type pred)))

    ;; Conjunction
    (conjunction? formula)
    (reduce (fn [e clause]
              (apply-formula e clause positive?))
            env
            (get-conjunction-clauses formula))

    ;; Disjunction
    (disjunction? formula)
    (let [refined-envs (map #(apply-formula env % positive?)
                           (get-disjunction-clauses formula))]
      ;; Combine all the environments
      (reduce merge-environments env refined-envs))

    ;; General negation - recursively apply with inverted positive flag
    (negation? formula)
    (apply-formula env (get-negation-formula formula) (not positive?))

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
    
    ;; Direct type keyword - handle types passed directly in tests
    (keyword? expr) expr

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
        ;; Special case for common operators that can take multiple arguments
        (contains? #{'< '> '= '+} fn-expr)
        (cond
          ;; Less than 2 arguments for operators that need at least 2
          (< (count args) 2)
          (throw (ex-info (str fn-expr " requires at least 2 arguments")
                         {:expr expr}))
          
          ;; Any number of arguments (2+)
          :else
          (let [;; Typecheck all arguments
                arg-types (mapv #(typecheck env %) args)]
            (cond
              ;; For comparison operators, all arguments must be numbers
              (contains? #{'< '> '=} fn-expr)
              (do
                ;; Verify all arguments are numbers for < and >
                (when (contains? #{'< '>} fn-expr)
                  (doseq [arg-type arg-types]
                    (when-not (subtype? arg-type int-type)
                      (throw (ex-info (str "Arguments to " fn-expr " must be numbers")
                                     {:arg-types arg-types})))))
                ;; Return boolean type
                bool-type)
              
              ;; For addition, all arguments must be numbers
              (= fn-expr '+)
              (do
                (doseq [arg-type arg-types]
                  (when-not (subtype? arg-type int-type)
                    (throw (ex-info "Arguments to + must be numbers"
                                   {:arg-types arg-types}))))
                ;; Return integer type
                int-type))))
        
        ;; For all other function applications
        :else
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
                          {:expr expr
                           :fn-type fn-type}))))))

    :else (throw (ex-info (str "Unsupported expression: " expr)
                         {:expr expr}))))

;;; ---- Testing ----

(defn -main [& args]
  (println "Core Logic Typing System")
  (println "To run the tests, use: lein test occur.core-logic-typing-test"))
