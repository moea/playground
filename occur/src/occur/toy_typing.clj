(ns occur.toy-typing)

;; Type definitions
(def int-type :int)
(def bool-type :bool)
(def string-type :string)

;; Type constructor for union types
(defn union-type [types]
  {:type :union
   :types (set types)})

;; Type predicates
(defn int-type? [t] (= t int-type))
(defn bool-type? [t] (= t bool-type))
(defn string-type? [t] (= t string-type))
(defn union-type? [t] (and (map? t) (= (:type t) :union)))

;; Type equality and subtyping
(defn type-equal? [t1 t2]
  (cond
    (and (keyword? t1) (keyword? t2)) (= t1 t2)
    (and (union-type? t1) (union-type? t2)) (= (:types t1) (:types t2))
    (and (union-type? t1) (keyword? t2)) (contains? (:types t1) t2)
    (and (keyword? t1) (union-type? t2)) (contains? (:types t2) t1)
    :else false))

(defn subtype? [t1 t2]
  (cond
    (type-equal? t1 t2) true
    (union-type? t2) (if (union-type? t1)
                       (every? #(contains? (:types t2) %) (:types t1))
                       (contains? (:types t2) t1))
    (union-type? t1) false
    :else false))

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
          (union-type #{then-type else-type}))
        (throw (ex-info "Condition must be a boolean" 
                        {:expr condition :type condition-type}))))
    
    :else (throw (ex-info (str "Unsupported expression: " expr) 
                          {:expr expr}))))

;; Example usage
(comment
  (typecheck {} 42)                                 ;; => :int
  (typecheck {} true)                               ;; => :bool
  (typecheck {} "hello")                            ;; => :string
  (typecheck {'x :int} 'x)                          ;; => :int
  (typecheck {} '(let [x 42] x))                    ;; => :int
  (typecheck {} '(let [x 42, y true] y))            ;; => :bool
  (typecheck {} '(union 42 "hello"))                ;; => {:type :union, :types #{:int :string}}
  (typecheck {} '(if true 42 "hello"))              ;; => {:type :union, :types #{:int :string}}
)
