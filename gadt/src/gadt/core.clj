(ns gadt.core
  (:require [clojure.string :as str]
            [clojure.walk   :as walk]))

(defrecord TypeVar  [name])
(defrecord TypeCtor [name tag params ret-type])
(defrecord Type     [name params])
(defrecord FuncType [params ret-type])

(defn type-var?    [t] (instance? TypeVar  t))
(defn type-ctor?   [t] (instance? TypeCtor t))
(defn type?        [t] (instance? Type     t))
(defn atomic-type? [t] (keyword? t))
(defn func-type?   [t] (instance? FuncType t))

(defn make-type-var [name]
  (->TypeVar name))
(defn make-type-ctor [name tag params ret-type]
  (->TypeCtor name tag params ret-type))
(defn make-type [name params]
  (->Type name params))
(defn make-func-type [param-types ret-type]
  (->FuncType param-types ret-type))

(defn env-lookup [env var]
  (or (env var)
      (throw (ex-info (str "Unbound identifier: " var) {:var var}))))

(defn type->str [type]
  (cond
    (atomic-type? type) (name type)
    (type-var? type)    (str "'" (:name type))
    (type-ctor? type)    (str (:name type) "." (:tag type))
    (type? type)        (let [args (str/join " " (map type->str (:params type)))]
                          (str "(" (:name type) " " args ")"))
    (func-type? type)   (let [param-strs (map type->str (:params type))
                              ret-str (type->str (:ret-type type))]
                          (str "(" (str/join " " param-strs) " -> " ret-str ")"))
    :else               (str type)))

(defn instantiate [type subst]
  (cond
    (type-var?  type) (subst type type)
    (type-ctor? type) (make-type-ctor
                       (:name type)
                       (:tag  type)
                       (map #(instantiate % subst) (:params type))
                       (instantiate (:ret-type type) subst))
    (type?      type) (make-type
                       (:name type)
                       (map #(instantiate % subst) (:params type)))
    (func-type? type) (make-func-type
                       (map #(instantiate % subst) (:params type))
                       (instantiate (:ret-type type) subst))
    :else             type))

(defn type-vars [type]
  (cond
    (type-var? type) #{type}
    (type-ctor? type) (into
                        (type-vars (:ret-type type))
                        (mapcat type-vars (:params type)))
    (type? type) (set (mapcat type-vars (:params type)))
    (func-type? type) (into
                        (type-vars (:ret-type type))
                        (mapcat type-vars (:params type)))
    :else #{}))

(declare unify)

(defn unify-pairwise [t1s t2s]
  (reduce
   (fn [subst [arg1 arg2]]
     (let [arg1'  (instantiate arg1 subst)
           arg2'  (instantiate arg2 subst)
           subst' (unify arg1' arg2')]
       (merge subst subst')))
   {}
   (map vector t1s t2s)))


(defn unify [t1 t2]
  (cond
    (= t1 t2) {}

    (type-var? t1)
    (if-not (contains? (type-vars t2) t1)
      {t1 t2}
      {})

    (type-var? t2)
    (if-not (contains? (type-vars t1) t2)
      {t2 t1}
      {})

    (and (type? t1)
         (type? t2)
         (= (:name t1)
            (:name t2))) (unify-pairwise (:params t1) (:params t2))

    (and (func-type? t1)
         (func-type? t2))
    (let [param-subst (unify-pairwise (:params t1) (:params t2))
          ret-subst   (unify (instantiate (:ret-type t1) param-subst)
                             (instantiate (:ret-type t2) param-subst))]
      (merge param-subst ret-subst))

    :else
    (throw (ex-info "Cannot unify" {:types [t1 t2]}))))

(defn try-unify [t1 t2]
  (try
    (unify t1 t2)
    (catch Exception _
      nil)))

(declare process-match-cases)

(def ^:dynamic *env*
  {'+   (make-func-type [:number :number] :number)
   '-   (make-func-type [:number :number] :number)
   '*   (make-func-type [:number :number] :number)
   'not (make-func-type [:bool] :bool)
   '=   (make-func-type [:number :number] :bool)})


(defn typecheck
  ([expr env]
   (cond
     (atomic-type? expr) expr
     (number?      expr) :number
     (string?      expr) :string
     (boolean?     expr) :bool
     (symbol?      expr) (env-lookup env expr)

     (and (list? expr) (= (first expr) 'match))
     (let [[_ expr & cases] expr
           expr-type   (typecheck expr env)]
       (or (process-match-cases env expr-type cases nil)
           (throw (ex-info "No matching cases in match expression" {:expr expr}))))

     (and (list? expr) (= (first expr) 'if))
     (let [[_ cond then else] expr
           cond-type (typecheck cond env)
           then-type (typecheck then env)
           else-type (typecheck else env)]
       (unify cond-type :bool)
       (let [result-subst (unify then-type else-type)]
         (instantiate then-type result-subst)))

     (and (list? expr) (symbol? (first expr)))
     (let [[ctor & args] expr
           ctor-type     (env-lookup env ctor)]
       (cond
         (type-ctor? ctor-type)
         (let [param-types (:params ctor-type)]
           (assert (= (count args) (count param-types)))
           (let [ret-type  (:ret-type ctor-type)
                 arg-types (map #(typecheck % env) args)
                 subst     (unify-pairwise param-types arg-types)]
             (instantiate ret-type subst)))

         (func-type? ctor-type)
         (let [param-types (:params ctor-type)]
           (assert (= (count args) (count param-types)))
           (let [ret-type  (:ret-type ctor-type)
                 arg-types (map #(typecheck % env) args)]
             (doseq [[param-type arg-type] (map vector param-types arg-types)]
               (try-unify param-type arg-type))
             ret-type))

         :else (throw (ex-info "Not a constructor or function"
                               {:expr expr}))))))
  ([expr] (typecheck expr *env*)))

(defn pattern-match [env pattern ty]
  (cond
    (= pattern '_)    env
    (symbol? pattern) (assoc env pattern ty)

    (and (list? pattern) (symbol? (first pattern)))
    (let [[ctor-name & sub-pats] pattern
          ctor-type              (try
                                   (env-lookup env ctor-name)
                                   (catch Exception _
                                     nil))]
      (when (and ctor-type (type-ctor? ctor-type))
        (let [param-types (:params ctor-type)
              ret-type    (:ret-type ctor-type)]
          (when (= (count sub-pats) (count param-types))
            (when-let [subst (try-unify ret-type ty)]
              (let [refined-params (map #(instantiate % subst) param-types)]
                (loop [env            env
                       [p & patterns] sub-pats
                       [t & types]    refined-params]
                  (if-not t
                    env
                    (when-let [env (pattern-match env p t)]
                      (recur env patterns types))))))))))

    (or (number?  pattern)
        (boolean? pattern)
        (string?  pattern))
    (if (try-unify (typecheck pattern env) ty)
      env
      nil)

    :else nil))

(defn process-match-cases [env ty cases result]
  (if (empty? cases)
    result
    (let [[[pat body] & rest-cases] cases]
      (if-let [refined-env (pattern-match env pat ty)]
        (let [body-type (typecheck body refined-env)
              result    (if result
                          (if (type-var? result)
                            result
                            (if (type-var? body-type)
                              body-type
                              (if-let [subst (try-unify result body-type)]
                                (instantiate result subst)
                                ty)))
                          body-type)]
          (process-match-cases env ty rest-cases result))
        (process-match-cases env ty rest-cases result)))))

(defn define-gadt [name type-params variants]
  (let [variants (map #(apply make-type-ctor name %) variants)]
    (reduce
     (fn reducer [e v]
       (assoc e (:tag v) v))
     {}
     variants)))

(defmacro declare-data-type [tname tvars & variants]
  (let [subst    (into {}
                   (for [tvar tvars]
                     [tvar (make-type-var tvar)]))
        variants (walk/postwalk
                  (fn walk [form]
                    (let [form (subst form form)]
                      (if (and (list? form)
                               (= tname (first form))
                               (not (vector? (second form))))
                        (make-type (first form) (rest form))
                        form)))
                  variants)]
    `(alter-var-root #'*env* merge (define-gadt
                                     (quote ~tname)
                                     (quote ~tvars)
                                     ~(into []
                                        (for [[name args ret] variants]
                                          `[(quote ~name) ~args ~ret]))))))

(defn type-expr->type [expr subst]
  (cond
    (keyword? expr) expr
    (symbol?  expr) (or (subst expr) expr)

    (list?    expr)
    (cond
      (= (first expr) '->)
      (let [[_ & types] expr
            param-types (butlast types)
            ret-type (last types)]
        (make-func-type
         (mapv #(type-expr->type % subst) param-types)
         (type-expr->type ret-type subst)))

      (vector? (second expr))
      expr

      (symbol? (first expr))
      (make-type (first expr) (mapv #(type-expr->type % subst) (rest expr)))

      :else expr)
    :else expr))

(defmacro tc-debug [expr]
  `(println (quote ~expr) "=>" (type->str (typecheck (quote ~expr)))))


(defmacro declare-fn [tvars name args ret-type body]
  (let [subst       (into {}
                      (for [tvar tvars]
                        [tvar (make-type-var tvar)]))
        arg-pairs   (partition 2 args)
        arg-names   (mapv first arg-pairs)
        arg-types   (mapv second arg-pairs)
        param-types (mapv #(type-expr->type % subst) arg-types)
        return-type (type-expr->type ret-type subst)
        fn-type     (make-func-type param-types return-type)]
    (alter-var-root #'*env* assoc name fn-type)
    (let [arg-env     (merge *env* (zipmap arg-names param-types))
          result-type (typecheck body arg-env)]
      (unify result-type return-type)
      (println "Typechecked function" name ":" (type->str fn-type)))))

(comment
  (declare-data-type Expr [A]
    (LitNum  [:number]         (Expr :number))
    (LitBool [:bool]           (Expr :bool))
    (Not     [(Expr :bool)]    (Expr :bool))
    (Add     [(Expr :number)
              (Expr :number)]  (Expr :number))
    (Eq?     [(Expr :number)
              (Expr :number)]  (Expr :bool))
    (If      [(Expr :bool)
              (Expr A)
              (Expr A)]        (Expr A)))

  (declare-fn [A] identity [x A] A
    x)

  (declare-fn [A] evaluate [x (Expr A)] A
    (match x
      [(LitNum n)  n]
      [(LitBool b) b]
      [(Not e)     (not (evaluate e))]
      [(Add e1 e2) (+ (evaluate e1) (evaluate e2))]
      [(Eq? e1 e2) (= (evaluate e1) (evaluate e2))]
      [(If cond then-expr else-expr)
       (if (evaluate cond)
         (evaluate then-expr)
         (evaluate else-expr))]))

  (declare-fn [] factorial [n :number] :number
    (if (= n 0)
      1
      (* n (factorial (- n 1))))))
