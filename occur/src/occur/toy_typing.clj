(ns occur.toy-typing)

;; Type definitions
(def int-type :int)
(def bool-type :bool)
(def string-type :string)
(def any-type :any)  ;; Top type - all values have this type

(declare union-type?)

;; Type constructor for union types
(defn union-type [types]
  {:type :union
   :types (set types)})

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

;; Default environment with built-in predicates and string-length function
(defn default-env []
  {'number? (function-type any-type bool-type)
   'boolean? (function-type any-type bool-type)
   'string? (function-type any-type bool-type)
   'string-length (function-type string-type int-type)})

;; Main typechecking function
(defn typecheck
  "Typechecks an expression with the given environment.
   Returns the type of the expression if successful, throws an error otherwise."
  [env expr]
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

    ;; If expression: (if condition then-expr else-expr)
    (and (seq? expr) (= (first expr) 'if))
    (let [condition (nth expr 1)
          then-expr (nth expr 2)
          else-expr (nth expr 3)
          condition-type (typecheck env condition)]
      (if (bool-type? condition-type)
        (let [then-type (typecheck env then-expr)
              else-type (typecheck env else-expr)]
          (union-merge then-type else-type))
        (throw (ex-info "Condition must be a boolean"
                        {:expr condition :type condition-type}))))

    ;; Function application: (f arg)
    (and (seq? expr) (= (count expr) 2))
    (let [fn-expr (first expr)
          arg-expr (second expr)
          fn-type (typecheck env fn-expr)
          arg-type (typecheck env arg-expr)]
      (if (function-type? fn-type)
        (if (subtype? arg-type (:param-type fn-type))
          (:return-type fn-type)
          (throw (ex-info "Argument type doesn't match parameter type"
                          {:fn-type fn-type
                           :arg-type arg-type})))
        (throw (ex-info "Applying a non-function"
                        {:expr expr
                         :fn-type fn-type}))))

    :else (throw (ex-info (str "Unsupported expression: " expr)
                          {:expr expr}))))

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
        (map expand-all form)
        form)
      ;; Expansion occurred, so recurse on the expanded form
      (expand-all expanded))))

;; Example usage
(comment
  (typecheck (default-env) 42)                      ;; => :int
  (typecheck (default-env) true)                    ;; => :bool
  (typecheck (default-env) "hello")                 ;; => :string
  (typecheck (merge (default-env) {'x :int}) 'x)    ;; => :int
  (typecheck (default-env) '(let [x 42] x))         ;; => :int
  (typecheck (default-env) '(let [x 42, y true] y)) ;; => :bool
  (typecheck (default-env) '(union 42 "hello"))     ;; => {:type :union, :types #{:int :string}}
  (typecheck (default-env) '(if true 42 "hello"))   ;; => {:type :union, :types #{:int :string}}
  (typecheck (default-env) '(number? 42))           ;; => :bool
  (typecheck (default-env) '(boolean? true))        ;; => :bool
  (typecheck (default-env) '(string? "hello"))      ;; => :bool
  (typecheck (default-env) '(let [x (union "string" 42)]
                              (if (string? x)
                                (string-length x)
                                x)))
  ;; Examples demonstrating any-type
  (subtype? int-type any-type)                      ;; => true
  (subtype? bool-type any-type)                     ;; => true
  (subtype? string-type any-type)                   ;; => true
  (subtype? (union-type #{int-type string-type}) any-type) ;; => true
  (subtype? any-type int-type)                      ;; => false
  ;; Union subtyping examples
  (subtype? int-type (union-type #{int-type string-type}))   ;; => true
  (subtype? string-type (union-type #{int-type string-type})) ;; => true
  (subtype? (union-type #{int-type}) (union-type #{int-type string-type})) ;; => true
  (subtype? (union-type #{int-type string-type}) string-type) ;; => false
  (subtype? (union-type #{string-type}) string-type) ;; => true
  ;; This should now fail to typecheck because union of string and int is not a subtype of string
  ;; Will throw: "Argument type doesn't match parameter type"
  (typecheck (default-env) '(let [x (union 42 "hello")] (string-length x)))
  ;; This should typecheck because we first narrow the union with a type test
  (typecheck (default-env) '(let [x (union 42 "hello")]
                              (if (string? x)
                                (string-length x)
                                0)))
  )
