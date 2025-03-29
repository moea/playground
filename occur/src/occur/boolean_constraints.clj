(ns occur.boolean-constraints
  (:require [clojure.core.logic :as l]
            [clojure.core.logic.pldb :as pldb]
            [clojure.set :as set]))

;;; ---- Boolean Formula Representation ----

;; Define data structures for boolean formulas
(defrecord TypeConstraint [var type])
(defrecord Conjunction [clauses])
(defrecord Disjunction [clauses])
(defrecord Negation [formula])

;; Smart constructors that simplify formulas
(defn make-conjunction [clauses]
  (let [flattened (mapcat (fn [c]
                            (if (instance? Conjunction c)
                              (:clauses c)
                              [c]))
                          clauses)
        filtered (filter (fn [c] (not= c true)) flattened)]
    (cond
      (some #(= % false) filtered) false
      (empty? filtered) true
      (= (count filtered) 1) (first filtered)
      :else (->Conjunction filtered))))

(defn make-disjunction [clauses]
  (let [flattened (mapcat (fn [c]
                            (if (instance? Disjunction c)
                              (:clauses c)
                              [c]))
                          clauses)
        filtered (filter (fn [c] (not= c false)) flattened)]
    (cond
      (some #(= % true) filtered) true
      (empty? filtered) false
      (= (count filtered) 1) (first filtered)
      :else (->Disjunction filtered))))

(defn make-negation [formula]
  (cond
    ;; Double negation elimination
    (instance? Negation formula) 
    (:formula formula)
    
    ;; De Morgan's laws
    (instance? Conjunction formula)
    (make-disjunction (map make-negation (:clauses formula)))
    
    (instance? Disjunction formula)
    (make-conjunction (map make-negation (:clauses formula)))
    
    ;; Boolean literals
    (= formula true) false
    (= formula false) true
    
    ;; Primitive
    :else (->Negation formula)))

(defn make-type-constraint [var type]
  (->TypeConstraint var type))

;;; ---- Boolean Formula Conversions ----

;; Convert to Negation Normal Form (only Ands, Ors and Nots around literals)
(defn to-nnf [formula]
  (cond
    ;; Primitives pass through
    (or (true? formula) (false? formula) (instance? TypeConstraint formula))
    formula
    
    ;; Push negation inward
    (instance? Negation formula)
    (let [inner (:formula formula)]
      (cond
        ;; Double negation elimination - handle nested cases better
        (instance? Negation inner) 
        (recur (to-nnf (:formula inner))) ; Recur to handle triple or more negations
        
        ;; De Morgan's laws
        (instance? Conjunction inner)
        (make-disjunction (map (comp to-nnf make-negation) (:clauses inner)))
        
        (instance? Disjunction inner)
        (make-conjunction (map (comp to-nnf make-negation) (:clauses inner)))
        
        ;; Negation of primitive
        :else (make-negation (to-nnf inner))))
    
    ;; Recursively convert composite formulas
    (instance? Conjunction formula)
    (make-conjunction (map to-nnf (:clauses formula)))
    
    (instance? Disjunction formula)
    (make-disjunction (map to-nnf (:clauses formula)))
    
    :else formula))

;; Convert formula to Conjunctive Normal Form (CNF)
(defn to-cnf [formula]
  (letfn [(distribute [disj conj]
            (make-conjunction
              (map #(make-disjunction (conj (:clauses disj) %))
                   (:clauses conj))))

          (cnf-step [f]
            (cond
              ;; Terminal cases
              (true? f) true
              (false? f) false
              (instance? TypeConstraint f) f
              (instance? Negation f) f

              ;; Already in CNF
              (instance? Conjunction f)
              (make-conjunction (map cnf-step (:clauses f)))

              ;; Need to distribute
              (instance? Disjunction f)
              (let [clauses (map cnf-step (:clauses f))
                    conj-clauses (filter #(instance? Conjunction %) clauses)
                    other-clauses (filter #(not (instance? Conjunction %)) clauses)]
                (if (empty? conj-clauses)
                  (make-disjunction other-clauses)
                  (let [first-conj (first conj-clauses)
                        remaining (concat other-clauses (rest conj-clauses))]
                    (if (empty? remaining)
                      first-conj
                      (cnf-step
                        (distribute
                          (make-disjunction remaining)
                          first-conj))))))

              :else f))]
    (cnf-step (to-nnf formula))))

;;; ---- Core.Logic Relations ----

;; Define placeholders for type system functions (will be replaced at runtime)
(def ^:dynamic subtype? nil)
(def ^:dynamic intersect-types nil)
(def ^:dynamic type-difference nil)
(def ^:dynamic union-type nil)

;; Define relation for checking if a formula is satisfied by an environment
(defn satisfied-o [formula env]
  (l/conde
    ;; Terminal cases
    [(l/== formula true) l/succeed]
    [(l/== formula false) l/fail]

    ;; Type constraint
    [(l/fresh [var type current-type]
       (l/== formula (->TypeConstraint var type))
       (l/project [var env]
         (let [current-type (get env var)]
           (if (subtype? current-type type)
             l/succeed
             l/fail))))]

    ;; Negation
    [(l/fresh [inner]
       (l/== formula (->Negation inner))
       (l/conda
         [(satisfied-o inner env) l/fail]
         [l/succeed]))]

    ;; Conjunction - all must be satisfied
    [(l/fresh [clauses]
       (l/== formula (->Conjunction clauses))
       (l/project [clauses]
         (l/everyg #(satisfied-o % env) clauses)))]

    ;; Disjunction - at least one must be satisfied
    [(l/fresh [clauses]
       (l/== formula (->Disjunction clauses))
       (l/project [clauses]
         (l/conde
           (map #(satisfied-o % env) clauses))))]))

;; Compute environment refinement given a constraint
(defn refine-env-o [env formula refined]
  (l/conde
    ;; Terminal cases
    [(l/== formula true) (l/== refined env)]
    [(l/== formula false) l/fail]  ;; Unsatisfiable constraint

    ;; Type constraint - refine the type
    [(l/fresh [var type]
       (l/== formula (->TypeConstraint var type))
       (l/project [var type env]
         (let [current-type (get env var)
               new-type (if current-type
                          (intersect-types current-type type)
                          type)]
           (if (= new-type :bottom)
             l/fail
             (l/== refined (assoc env var new-type))))))]

    ;; Negation
    [(l/fresh [inner var type]
       (l/== formula (->Negation (->TypeConstraint var type)))
       (l/project [var type env]
         (let [current-type (get env var)
               new-type (if current-type
                          (type-difference current-type type)
                          nil)]
           (if (or (nil? new-type) (= new-type :bottom))
             l/fail
             (l/== refined (assoc env var new-type))))))]

    ;; Conjunction - refine through each clause sequentially
    [(l/fresh [clauses intermediate-envs final-env]
       (l/== formula (->Conjunction clauses))
       (l/project [clauses env]
         (let [result (reduce (fn [e clause]
                                (let [solutions (l/run 1 [q] (refine-env-o e clause q))]
                                  (if (empty? solutions)
                                    (reduced nil) ;; Short-circuit if unsatisfiable
                                    (first solutions))))
                              env
                              clauses)]
           (if (nil? result)
             l/fail
             (l/== refined result)))))]

    ;; Disjunction - branch and take union of types
    [(l/fresh [clauses branch-envs]
       (l/== formula (->Disjunction clauses))
       (l/project [clauses env]
         ;; Get refined env for each branch
         (let [all-envs (map (fn [clause]
                               (l/run* [q]
                                 (refine-env-o env clause q)))
                             clauses)
               ;; Combine environments by taking union of possible types for each variable
               combined (if (some empty? all-envs)
                          env  ;; Some branch is unsatisfiable, keep original env
                          (let [merged-env (reduce (fn [acc branch-env]
                                                    (if (empty? branch-env)
                                                      acc  ;; Skip empty branches
                                                      (let [branch (first branch-env)] ;; Take first solution
                                                        (reduce-kv (fn [result k v]
                                                                     (if-let [curr-type (get result k)]
                                                                       ;; Merge with union-type
                                                                       (assoc result k (union-type #{curr-type v}))
                                                                       ;; New variable in this branch
                                                                       (assoc result k v)))
                                                                   acc
                                                                   branch))))
                                                  {}  ;; Start with empty environment
                                                  all-envs)
                                ;; For any vars in original env not in any branch, keep original value
                                final-env (reduce-kv (fn [result k v]
                                                      (if (contains? result k)
                                                        result  ;; Already merged from branches
                                                        (assoc result k v)))  ;; Keep original
                                                    merged-env
                                                    env)]
                            final-env))]
           (l/== refined combined))))]))

;;; ---- Constraint Solving Interface ----

;; Convert our constraint structure to boolean formulas
(defn constraint->formula [constraint]
  (case (:op constraint)
    :is (make-type-constraint (:var constraint) (:type constraint))
    :not (make-negation (make-type-constraint (:var constraint) (:type constraint)))
    :and (make-conjunction (map constraint->formula (:constraints constraint)))
    :or (make-disjunction (map constraint->formula (:constraints constraint)))))

;; Solve a boolean constraint system
(defn solve-constraint-system [env constraints]
  (if (empty? constraints)
    env
    ;; Convert to formulas and combine with AND
    (let [formulas (map constraint->formula constraints)
          formula (make-conjunction formulas)
          ;; Convert to CNF for more efficient solving
          cnf (to-cnf formula)
          ;; Use core.logic to find a solution
          solutions (l/run 1 [q]
                      (refine-env-o env cnf q))]
      (if (empty? solutions)
        env  ;; No solution, constraint is unsatisfiable
        (first solutions)))))

;;; ---- Integration with Type System ----

;; Replace original constraint solving with boolean constraint solver
(defn solve-with-boolean-logic [env constraints positive?]
  (if positive?
    (solve-constraint-system env constraints)
    ;; For negated path, negate all constraints
    (let [negated (map (fn [c]
                         (case (:op c)
                           :is {:op :not :var (:var c) :type (:type c)}
                           :not {:op :is :var (:var c) :type (:type c)}
                           :and {:op :or
                                 :constraints (map (fn [subc]
                                                     (case (:op subc)
                                                       :is {:op :not :var (:var subc) :type (:type subc)}
                                                       :not {:op :is :var (:var subc) :type (:type subc)}
                                                       subc))
                                                   (:constraints c))}
                           :or {:op :and
                                :constraints (map (fn [subc]
                                                    (case (:op subc)
                                                      :is {:op :not :var (:var subc) :type (:type subc)}
                                                      :not {:op :is :var (:var subc) :type (:type subc)}
                                                      subc))
                                                  (:constraints c))}))
                       constraints)]
      (solve-constraint-system env negated))))

;; Extract constraints from expressions directly
(defn extract-constraints-from-expr [expr pred-map]
  (cond
    ;; Literal values - no constraints
    (or (integer? expr) (string? expr) (boolean? expr) (nil? expr))
    nil

    ;; Variable reference - no constraints
    (symbol? expr)
    nil

    ;; Sequence expressions
    (seq? expr)
    (case (first expr)
      ;; Direct 'not' application
      not (let [inner (extract-constraints-from-expr (second expr) pred-map)]
            (if inner
              (make-negation inner)
              nil))

      ;; 'and' expression
      and (let [inner-constraints (keep #(extract-constraints-from-expr % pred-map) (rest expr))]
            (if (not-empty inner-constraints)
              (make-conjunction inner-constraints)
              nil))

      ;; 'or' expression
      or (let [inner-constraints (keep #(extract-constraints-from-expr % pred-map) (rest expr))]
           (if (not-empty inner-constraints)
             (make-disjunction inner-constraints)
             nil))

      ;; Equality expressions - special handling
      = (if (and (= (count expr) 3)
                (symbol? (second expr))
                (or (boolean? (nth expr 2)) (nil? (nth expr 2))))
          ;; Handle (= x true/false/nil) expressions
          (let [var (second expr)
                val (nth expr 2)]
            (if (boolean? val)
              ;; Both true and false constrain to boolean type
              (make-type-constraint var :bool)
              ;; (= x nil) is equivalent to (nil? x)
              (make-type-constraint var :nil)))
          ;; Other equality expressions - we don't extract constraints
          nil)

      ;; If expression (could be a negation pattern)
      if (if (and (= (count expr) 4)
                  (= (nth expr 2) false)
                  (= (nth expr 3) true))
           ;; (if pred false true) is equivalent to (not pred)
           (let [inner (extract-constraints-from-expr (second expr) pred-map)]
             (if inner
               (make-negation inner)
               nil))
           ;; Regular if - just extract from condition
           (extract-constraints-from-expr (second expr) pred-map))

      ;; Type predicate
      (if-let [type (get pred-map (first expr))]
        (if (fn? type)
          ;; For function-valued predicates (like =)
          (type expr pred-map)
          ;; For simple type predicates
          (when (= (count expr) 2)
            (make-type-constraint (second expr) type)))
        ;; Not a predicate we recognize
        nil))

    ;; Default
    :else nil))

;; Function to integrate with existing system
(defn create-boolean-constraint-solver [subtype-fn intersect-fn difference-fn union-fn]
  (alter-var-root #'occur.boolean-constraints/subtype? (constantly subtype-fn))
  (alter-var-root #'occur.boolean-constraints/intersect-types (constantly intersect-fn))
  (alter-var-root #'occur.boolean-constraints/type-difference (constantly difference-fn))
  (alter-var-root #'occur.boolean-constraints/union-type (constantly union-fn))

  ;; Return a function that processes either constraints or direct expressions
  (fn [env expr-or-constraints positive?]
    (cond
      ;; If it's a direct expression, extract constraints first
      (and (not (vector? expr-or-constraints))
           (not (map? expr-or-constraints)))
      (let [pred-map {'string? :string
                      'number? :int
                      'boolean? :bool
                      '= (fn [expr _]
                           ;; Handle (= x true/false) as a special case
                           (when (and (= (count expr) 3)
                                      (symbol? (second expr))
                                      (boolean? (nth expr 2)))
                             (let [var (second expr)]
                               ;; Both true and false checks just constrain to boolean type
                               ;; For more sophisticated handling, we'd need to track the exact boolean value
                               (make-type-constraint var :bool))))}
            formula (extract-constraints-from-expr expr-or-constraints pred-map)]
        (if formula
          (let [formula-to-use (if positive?
                                 formula
                                 (make-negation formula))
                cnf (to-cnf formula-to-use)
                solutions (l/run 1 [q]
                            (refine-env-o env cnf q))]
            (if (empty? solutions)
              env
              (first solutions)))
          env))

      ;; If it's a list of constraint maps, use the original method
      :else (solve-with-boolean-logic env expr-or-constraints positive?))))
