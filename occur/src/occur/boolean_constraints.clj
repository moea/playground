(ns occur.boolean-constraints
  (:require [clojure.set :as set]))

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
    (instance? Negation formula) (:formula formula)

    ;; De Morgan's laws
    (instance? Conjunction formula)
    (make-disjunction (map make-negation (:clauses formula)))

    (instance? Disjunction formula)
    (make-conjunction (map make-negation (:clauses formula)))

    ;; Primitive
    :else (->Negation formula)))

(defn make-type-constraint [var type]
  (->TypeConstraint var type))

;;; ---- Boolean Formula Conversions ----

;; Convert to Negation Normal Form (NNF) - negations only at atoms
(defn to-nnf [formula]
  (cond
    ;; Primitive cases
    (true? formula) true
    (false? formula) false
    (instance? TypeConstraint formula) formula

    ;; Negation - push down using De Morgan's laws
    (instance? Negation formula)
    (let [inner (:formula formula)]
      (cond
        (instance? Conjunction inner)
        (make-disjunction (map (comp to-nnf make-negation) (:clauses inner)))

        (instance? Disjunction inner)
        (make-conjunction (map (comp to-nnf make-negation) (:clauses inner)))

        (instance? Negation inner)
        (to-nnf (:formula inner))

        ;; Primitive negation
        :else (make-negation (to-nnf inner))))

    ;; Complex cases
    (instance? Conjunction formula)
    (make-conjunction (map to-nnf (:clauses formula)))

    (instance? Disjunction formula)
    (make-disjunction (map to-nnf (:clauses formula)))

    :else formula))

;;; ---- Integration with Type System ----

;; Function to integrate with existing system
;; This is kept to maintain compatibility with core_logic_typing.clj
;; even though the actual implementation is in that file
(defn create-boolean-constraint-solver [subtype-fn intersect-fn difference-fn union-fn]
  ;; Return an identity function that does nothing
  (fn [env _ _]
    env))
