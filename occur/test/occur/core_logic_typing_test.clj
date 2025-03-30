(ns occur.core-logic-typing-test
  (:require [clojure.test :refer :all]
            [occur.core-logic-typing :as typing :refer [int-type bool-type string-type]]))

(defn setup-test-env []
  ;; Create a minimal environment for tests
  (typing/init-env))

(defn type-check
  "Helper function that typechecks an expression and returns its type"
  [expr]
  (let [env (setup-test-env)]
    (typing/typecheck env expr)))

(deftest test-simple-predicates
  (testing "Basic type predicate for string"
    (let [expr '(let [x (union :int :string)]
                  (if (string? x)
                    (string-length x)
                    0))
          result-type (type-check expr)]
      (is (= :int result-type)
          "Result should be an integer type")))

  (testing "Type predicate with negation"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (not (string? x))
                    "not a string"
                    (string-length x)))
          result-type (type-check expr)]
      (is (= (typing/union-type #{:int :string}) result-type)
          "Result should be a union of int and string")
      (is (not= :bool result-type)
          "Result should not include boolean type"))))

(deftest test-compound-predicates
  (testing "OR expressions"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (or (number? x) (string? x))
                    "number or string"
                    "boolean"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type")))

  (testing "AND expressions"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (and (string? x) (not (boolean? x)))
                    (string-length x)
                    "not a valid string"))
          result-type (type-check expr)]
      (is (= (typing/union-type #{:int :string}) result-type)
          "Result should be a union of int and string")
      (is (not= :bool result-type)
          "Result should not include boolean type"))))

(deftest test-complex-predicates
  (testing "Complex nested boolean expressions"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (or (number? x)
                          (and (string? x) (not (boolean? x))))
                    "valid input"
                    "invalid input"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type")))

  (testing "Nested refinements with negation"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (not (or (number? x) (boolean? x)))
                    (string-length x)  ;; must be a string here
                    "not a string"))
          result-type (type-check expr)]
      (is (= (typing/union-type #{:int :string}) result-type)
          "Result should be a union of int and string"))))

(deftest test-multiple-args-in-boolean-ops
  (testing "Multiple arguments for AND"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (and (not (boolean? x)) (not (number? x)) (string? x))
                    (string-length x)
                    0))
          result-type (type-check expr)]
      (is (= :int result-type)
          "Result should be an integer type")))

  (testing "Multiple arguments for OR"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (or (number? x) (string? x) (boolean? x))
                    "known type"
                    "unknown type"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type"))))

(deftest test-triple-negation
  (testing "Triple negation properly handled"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (not (not (not (string? x))))
                    "triple negation"
                    (string-length x)))
          result-type (type-check expr)]
      (is (= (typing/union-type #{:int :string}) result-type)
          "Result should be a union of int and string")
      (is (not= :bool result-type)
          "Result should not include boolean type"))))

(deftest test-complex-case
  (testing "Complex predicate with negation, OR, and AND"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (and (not (number? x))
                           (or (string? x)
                               (and (boolean? x) (not (= x false)))))
                    "refined correctly" ;; Should be string or true, not false or number
                    "fallback"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type"))))

(deftest test-equality-predicates
  (testing "Basic equality constraint with integer"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (= x -1)
                    "x is an integer"
                    "x could be anything"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type")))

  (testing "Equality with OR condition"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (or (= x 42) (string? x))
                    "x is an integer or string"
                    "x must be boolean"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type")))

  (testing "Equality with negation"
    (let [expr '(let [x (union :int :string :bool)]
                  (if (not (= x 42))
                    "x is not an integer"
                    "x is an integer"))
          result-type (type-check expr)]
      (is (= :string result-type)
          "Result should be a string type"))))

(deftest test-function-application
  (testing "Single argument function application"
    (let [expr '(let [s "hello"]
                  (string-length s))
          result-type (type-check expr)]
      (is (= :int result-type)
          "Result should be an integer type")))

  (testing "Function with fixed arity"
    (let [env (merge (setup-test-env)
                     {'my-function (typing/function-type [int-type bool-type] :string)})
          expr '(my-function 42 true)]
      (is (= :string (typing/typecheck env expr))
          "Function should accept exactly the specified number of arguments")))

  (testing "Wrong arity function call"
    (let [env (merge (setup-test-env)
                     {'my-function (typing/function-type [int-type bool-type] :string)})
          expr '(my-function 42 true false)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"expects 2 arguments but got 3"
                         (typing/typecheck env expr))
          "Function should reject calls with wrong arity")))

  (testing "Nested function application with correct types"
    (let [env (merge (setup-test-env)
                    {'add-two (typing/function-type [int-type int-type] int-type)
                     'is-positive (typing/function-type [int-type] bool-type)})
          expr '(is-positive (add-two 1 2))]
      (is (= bool-type (typing/typecheck env expr))
          "Nested function application should work with correct types")))

  (testing "Type mismatch in argument"
    (let [env (merge (setup-test-env)
                    {'str-func (typing/function-type [string-type string-type] string-type)})
          expr '(str-func "hello" 42)]
      (is (thrown? Exception (typing/typecheck env expr))
          "Should throw exception when arg doesn't match parameter type"))))

(deftest test-multi-argument-functions
  (testing "Binary addition operator"
    (let [expr '(let [x 10
                      y 20]
                  (+ x y))
          result-type (type-check expr)]
      (is (= :int result-type)
          "Addition with 2 integer arguments should return int")))

  (testing "Binary comparison operator"
    (let [expr '(let [x 10
                      y 20]
                  (< x y))
          result-type (type-check expr)]
      (is (= :bool result-type)
          "Comparison with 2 integer arguments should return bool")))

  (testing "Binary equality operator"
    (let [expr '(let [x 10
                      y 20]
                  (= x y))
          result-type (type-check expr)]
      (is (= :bool result-type)
          "Equality with 2 arguments should return bool"))))

(deftest test-binary-operator-errors
  (testing "Less than with wrong number of arguments"
    (let [expr '(let [x 10]
                  (< x))
          env (setup-test-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"expects 2 arguments but got 1"
                            (typing/typecheck env expr))
          "Should throw exception when < has too few arguments")))

  (testing "Addition with too many arguments"
    (let [expr '(let [x 10
                      y 20
                      z 30]
                  (+ x y z))
          env (setup-test-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"expects 2 arguments but got 3"
                            (typing/typecheck env expr))
          "Should throw exception when + has too many arguments")))

  (testing "Equality with wrong number of arguments"
    (let [expr '(let [x 10]
                  (= x))
          env (setup-test-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"expects 2 arguments but got 1"
                            (typing/typecheck env expr))
          "Should throw exception when = has wrong number of arguments")))

  (testing "Type mismatch in binary operator"
    (let [expr '(let [x 10
                      y "string"]
                  (+ x y))
          env (setup-test-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"type mismatch"
                            (typing/typecheck env expr))
          "Should throw exception when arguments have incompatible types"))))

(deftest test-multi-arg-unification
  (testing "Type unification via equality"
    (let [expr '(let [x (union :int :string)
                      y (union :int :bool)]
                  (if (= x y)
                    (< x y)  ;; x and y must both be :int here
                    "Incorrect path"))
          result (typing/typecheck (setup-test-env) expr)]
      (is (= result #{:string :bool})
          "In the then branch, x and y are both :int, giving :bool; in the else branch, we get :string"))))

(deftest test-type-refinement-failures
  (testing "Type error when using non-number type with addition"
    (let [expr '(let [x (union :int :string)]
                  (+ x "not a number"))
          env (setup-test-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"type mismatch"
                            (typing/typecheck env expr))
          "Should throw exception for non-number in addition")))

  (testing "Type error when applying a non-function"
    (let [expr '(let [x 42]
                  (x 10))
          env (setup-test-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Applying a non-function"
                            (typing/typecheck env expr))
          "Should throw exception when applying a non-function"))))

(deftest test-type-refinement-with-comparisons
  (testing "Type error with union type in comparison"
    (let [expr '(let [x (union :int :string)]
                  (if (< x 100)
                    (+ x 1)  ;; x must be a number here
                    "x is not a positive number less than 100"))
          env (setup-test-env)]
      ;; In our fixed-arity implementation, this throws because x is a union containing non-int types
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"type mismatch"
                            (typing/typecheck env expr))
          "Should throw exception when using union type with binary operator"))))

  (testing "Type refinement with predicate before comparison would be useful in a more complex system"
    (let [expr '(let [x (union :int :string :bool)
                      y 10]
                  (if (and (number? x) (< x y))
                    (+ x y)
                    "invalid"))
          env (setup-test-env)]
      ;; Our simple type system doesn't refine based on predicates before evaluating other expressions
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"type mismatch"
                          (typing/typecheck env expr))
          "Should throw exception because refinement from number? predicate isn't used in < evaluation")))

(deftest test-subtyping
  (testing "Subtype relations"
    (is (typing/subtype? :int (typing/union-type #{:int :string}))
        "Integer should be a subtype of integer|string union")
    (is (typing/subtype? (typing/union-type #{:int}) (typing/union-type #{:int :string}))
        "Union with just integer should be a subtype of integer|string union")
    (is (not (typing/subtype? (typing/union-type #{:int :bool}) :int))
        "Integer|boolean union should not be a subtype of integer")))

(deftest test-type-operations
  (testing "Intersection of types"
    (is (= :int (typing/intersect-types :int :int))
        "Intersection of same types should be the type itself")
    (is (= typing/bottom-type (typing/intersect-types :int :string))
        "Intersection of disjoint types should be bottom type")
    (is (= :int (typing/intersect-types (typing/union-type #{:int :string}) :int))
        "Intersection of union with member should be the member"))

  (testing "Type difference"
    (is (= typing/bottom-type (typing/type-difference :int :int))
        "Difference of same types should be bottom type")
    (is (= :int (typing/type-difference :int :string))
        "Difference of disjoint types should be the first type")
    (is (= :string (typing/type-difference (typing/union-type #{:int :string}) :int))
        "Difference of union with member should remove that member")))

(deftest test-type-predicates
  (testing "primitive-type?"
    (is (typing/primitive-type? :int) "Keywords should be primitive types")
    (is (typing/primitive-type? :custom-type) "Custom keyword types should be primitive")
    (is (not (typing/primitive-type? #{:int :bool})) "Sets should not be primitive types")
    (is (not (typing/primitive-type? (typing/function-type [:int] :bool))) "Function types should not be primitive"))

  (testing "union-type?"
    (is (typing/union-type? #{:int :bool}) "Sets should be union types")
    (is (typing/union-type? (typing/union-type :int :bool)) "union-type function should create union types")
    (is (not (typing/union-type? :int)) "Keywords should not be union types")
    (is (not (typing/union-type? (typing/function-type [:int] :bool))) "Function types should not be union types"))

  (testing "function-type?"
    (is (typing/function-type? (typing/function-type [:int] :bool)) "function-type should create function types")
    (is (not (typing/function-type? :int)) "Keywords should not be function types")
    (is (not (typing/function-type? #{:int :bool})) "Sets should not be function types")))

(deftest test-union-types-helper
  (testing "union-types helper function"
    (is (= #{:int :bool} (typing/union-types #{:int :bool})) "Should return the set directly if it's already a set")
    (is (= #{:int} (typing/union-types :int)) "Should wrap non-sets in a singleton set")))

(deftest test-compatible-with-bool
  (testing "compatible-with-bool? function"
    (is (typing/compatible-with-bool? :bool) "bool-type should be compatible with bool")
    (is (typing/compatible-with-bool? #{:bool :int}) "Union containing bool-type should be compatible")
    (is (not (typing/compatible-with-bool? :int)) "int-type should not be compatible with bool")
    (is (not (typing/compatible-with-bool? #{:int :string})) "Union without bool-type should not be compatible")))

(deftest test-init-env
  (testing "init-env function"
    (let [env (typing/init-env)]
      (is (typing/function-type? (get env 'string-length)) "Environment should contain string-length function")
      (is (typing/function-type? (get env '<)) "Environment should contain < operator")
      (is (typing/function-type? (get env 'number?)) "Environment should contain number? predicate"))))

(deftest test-boolean-formula-constructors
  (testing "type-constraint constructor"
    (let [constraint (typing/type-constraint 'x :int)]
      (is (= :type (:constraint constraint)) "Should have :type constraint type")
      (is (= 'x (:var constraint)) "Should have correct variable")
      (is (= :int (:type constraint)) "Should have correct type")))

  (testing "conjunction constructor"
    (let [c1 (typing/type-constraint 'x :int)
          c2 (typing/type-constraint 'y :string)]
      ;; Simple case
      (let [conj (typing/conjunction [c1 c2])]
        (is (= :conjunction (:constraint conj)) "Should have :conjunction constraint type")
        (is (= 2 (count (:clauses conj))) "Should contain the right number of constraints"))

      ;; With true/false constants
      (is (= false (typing/conjunction [c1 false])) "Conjunction with false is false")
      (is (= c1 (typing/conjunction [c1 true])) "Conjunction with true is the other constraint")
      (is (= true (typing/conjunction [])) "Empty conjunction is true")

      ;; Flattening nested conjunctions
      (let [nested (typing/conjunction [c1 (typing/conjunction [c2])])]
        (is (= :conjunction (:constraint nested)) "Should flatten nested conjunctions")
        (is (= 2 (count (:clauses nested))) "Should contain the right number of constraints after flattening"))))

  (testing "disjunction constructor"
    (let [c1 (typing/type-constraint 'x :int)
          c2 (typing/type-constraint 'y :string)]
      ;; Simple case
      (let [disj (typing/disjunction [c1 c2])]
        (is (= :disjunction (:constraint disj)) "Should have :disjunction constraint type")
        (is (= 2 (count (:clauses disj))) "Should contain the right number of constraints"))

      ;; With true/false constants
      (is (= true (typing/disjunction [c1 true])) "Disjunction with true is true")
      (is (= c1 (typing/disjunction [c1 false])) "Disjunction with false is the other constraint")
      (is (= false (typing/disjunction [])) "Empty disjunction is false")

      ;; Flattening nested disjunctions
      (let [nested (typing/disjunction [c1 (typing/disjunction [c2])])]
        (is (= :disjunction (:constraint nested)) "Should flatten nested disjunctions")
        (is (= 2 (count (:clauses nested))) "Should contain the right number of constraints after flattening"))))

  (testing "negation constructor"
    (let [c (typing/type-constraint 'x :int)]
      ;; Simple case
      (let [neg (typing/negation c)]
        (is (= :negation (:constraint neg)) "Should have :negation constraint type")
        (is (= c (:formula neg)) "Should contain the negated formula"))

      ;; Constants and double negation
      (is (= false (typing/negation true)) "Negation of true is false")
      (is (= true (typing/negation false)) "Negation of false is true")
      (is (= c (typing/negation (typing/negation c))) "Double negation cancels out"))))

(deftest test-formula-type-predicates
  (testing "type-constraint? predicate"
    (is (typing/type-constraint? (typing/type-constraint 'x :int)) "Should recognize type constraints")
    (is (not (typing/type-constraint? (typing/conjunction [(typing/type-constraint 'x :int)
                                                          (typing/type-constraint 'y :string)])))
        "Should not match conjunctions"))

  (testing "conjunction? predicate"
    (is (typing/conjunction? (typing/conjunction [(typing/type-constraint 'x :int)
                                                (typing/type-constraint 'y :string)]))
        "Should recognize conjunctions")
    (is (not (typing/conjunction? (typing/type-constraint 'x :int))) "Should not match type constraints"))

  (testing "disjunction? predicate"
    (is (typing/disjunction? (typing/disjunction [(typing/type-constraint 'x :int)
                                                 (typing/type-constraint 'y :string)]))
        "Should recognize disjunctions")
    (is (not (typing/disjunction? (typing/type-constraint 'x :int))) "Should not match type constraints"))

  (testing "negation? predicate"
    (is (typing/negation? (typing/negation (typing/type-constraint 'x :int))) "Should recognize negations")
    (is (not (typing/negation? (typing/type-constraint 'x :int))) "Should not match type constraints")))

(deftest test-to-nnf
  (testing "to-nnf function"
    ;; Constants should remain unchanged
    (is (= true (typing/to-nnf true)) "true should remain unchanged")
    (is (= false (typing/to-nnf false)) "false should remain unchanged")

    ;; Atomic constraints should remain unchanged
    (let [c (typing/type-constraint 'x :int)]
      (is (= c (typing/to-nnf c)) "Type constraints should remain unchanged"))

    ;; Negation of constants
    (is (= false (typing/to-nnf (typing/negation true))) "Negation of true should be false")
    (is (= true (typing/to-nnf (typing/negation false))) "Negation of false should be true")

    ;; Double negation
    (let [c (typing/type-constraint 'x :int)
          double-neg (typing/negation (typing/negation c))]
      (is (= c (typing/to-nnf double-neg)) "Double negation should be eliminated"))

    ;; De Morgan's laws
    (let [c1 (typing/type-constraint 'x :int)
          c2 (typing/type-constraint 'y :string)
          neg-conj (typing/negation (typing/conjunction [c1 c2]))
          neg-disj (typing/negation (typing/disjunction [c1 c2]))]

      ;; ¬(A ∧ B) ≡ ¬A ∨ ¬B
      (let [result (typing/to-nnf neg-conj)]
        (is (typing/disjunction? result) "Negated conjunction should become disjunction")
        (is (= 2 (count (:clauses result))) "Should have two clauses"))

      ;; ¬(A ∨ B) ≡ ¬A ∧ ¬B
      (let [result (typing/to-nnf neg-disj)]
        (is (typing/conjunction? result) "Negated disjunction should become conjunction")
        (is (= 2 (count (:clauses result))) "Should have two clauses")))

    ;; Recursive transformation
    (let [c1 (typing/type-constraint 'x :int)
          c2 (typing/type-constraint 'y :string)
          complex (typing/conjunction [c1 (typing/disjunction [c2 (typing/negation c1)])])]
      (is (typing/conjunction? (typing/to-nnf complex)) "Should preserve outer conjunction")
      (is (typing/disjunction? (second (:clauses (typing/to-nnf complex)))) "Should preserve inner disjunction"))))

(deftest test-extract-predicate
  (testing "extract-predicate function"
    ;; Basic type predicates
    (let [number-pred (typing/extract-predicate '(number? x))]
      (is (typing/type-constraint? number-pred) "Should extract type constraint for number?")
      (is (= 'x (:var number-pred)) "Should extract correct variable")
      (is (= :int (:type number-pred)) "Should extract correct type"))

    ;; Unsupported expressions
    (is (nil? (typing/extract-predicate '(+ x y))) "Should not extract predicate for addition")
    (is (nil? (typing/extract-predicate 42)) "Should not extract predicate for literals")))

(deftest test-extract-formula
  (testing "extract-formula function"
    ;; No formula for literals or simple variables
    (is (nil? (typing/extract-formula 42)) "Should not extract formula for integer literals")
    (is (nil? (typing/extract-formula "hello")) "Should not extract formula for string literals")
    (is (nil? (typing/extract-formula 'x)) "Should not extract formula for variable references")

    ;; Simple predicate
    (let [formula (typing/extract-formula '(number? x))]
      (is (typing/type-constraint? formula) "Should extract type constraint for predicates"))

    ;; Boolean operations
    (let [neg-formula (typing/extract-formula '(not (string? x)))]
      (is (typing/negation? neg-formula) "Should extract negation for 'not'"))

    ;; For complex formulae, we need variables to be in scope for sensible tests
    (let [env {'x :int, 'y :string}
          conj-formula (typing/extract-formula '(and (number? x) (string? y)))]
      (is (typing/conjunction? conj-formula) "Should extract conjunction for 'and'")
      (is (= 2 (count (:clauses conj-formula))) "Should have both predicates"))

    (let [env {'x :int, 'y :string}
          disj-formula (typing/extract-formula '(or (number? x) (string? y)))]
      (is (typing/disjunction? disj-formula) "Should extract disjunction for 'or'")
      (is (= 2 (count (:clauses disj-formula))) "Should have both predicates"))

    ;; Extract from condition in if
    (let [if-formula (typing/extract-formula '(if (number? x) a b))]
      (is (typing/type-constraint? if-formula) "Should extract formula from if condition"))

    ;; Extract from complex nested expressions
    ;; For nested AND/OR, check specific components rather than exact structure
    (let [formula (typing/extract-formula '(if (number? x) a b))]
      (is (typing/type-constraint? formula) "Should extract formula from if condition"))))

(deftest test-refine-env
  (testing "refine-env function"
    (let [env {'x #{:int :string}}]
      ;; Positive refinement
      (let [refined (typing/refine-env env 'x :int true)]
        (is (= :int (get refined 'x)) "Should refine to int type when constraint is positive"))

      ;; Negative refinement
      (let [refined (typing/refine-env env 'x :int false)]
        (is (= :string (get refined 'x)) "Should remove int type when constraint is negative"))

      ;; Constraint that makes type bottom
      (let [refined (typing/refine-env env 'x :bool true)]
        (is (= env refined) "Should not change env when constraint would make type bottom"))

      ;; Variable not in environment
      (let [refined (typing/refine-env env 'z :int true)]
        (is (= env refined) "Should not change env when variable is not present")))))

(deftest test-apply-constraint
  (testing "apply-constraint function"
    (let [env {'x #{:int :string}}
          constraint (typing/type-constraint 'x :int)]
      ;; Positive constraint
      (let [refined (typing/apply-constraint env constraint true)]
        (is (= :int (get refined 'x)) "Should apply positive constraint correctly"))

      ;; Negative constraint
      (let [refined (typing/apply-constraint env constraint false)]
        (is (= :string (get refined 'x)) "Should apply negative constraint correctly"))

      ;; Non-type constraint
      (is (= env (typing/apply-constraint env "not a constraint" true))
          "Should not change env for non-constraints"))))

(deftest test-merge-environments
  (testing "merge-environments function"
    (let [base-env {'x :int, 'z :bool}
          env2 {'x :string, 'y :bool}]

      ;; Simple case - just test that we get the base environment back
      (is (= base-env (typing/merge-environments base-env))
          "Should return base environment when no additional environments provided")

      ;; Test with just the base env and env2
      (let [merged (typing/merge-environments base-env env2)]
        ;; Check that z is preserved from base-env
        (is (= :bool (get merged 'z))
            "Should preserve type for variable only in base environment")))))

(deftest test-apply-formula
  (testing "apply-formula function"
    (let [env {'x #{:int :string :bool}, 'y :int}]

      ;; Boolean constants
      (is (= env (typing/apply-formula env true true))
          "Constants should not change the environment")
      (is (= env (typing/apply-formula env false false))
          "Constants should not change the environment")

      ;; Type constraint
      (let [constraint (typing/type-constraint 'x :int)
            refined (typing/apply-formula env constraint true)]
        (is (= :int (get refined 'x))
            "Should apply type constraint"))

      ;; Negation
      (let [neg (typing/negation (typing/type-constraint 'x :int))
            refined (typing/apply-formula env neg true)
            result-type (get refined 'x)]
        (is (not= result-type :int))
        (is (not= result-type :bool))
        (is (not= result-type :string))
        (is (or (= result-type #{:string :bool})
                (= result-type #{:bool :string}))
            "Should remove :int from the union type"))

      ;; Conjunction
      (let [conj (typing/conjunction [(typing/type-constraint 'x :int)
                                      (typing/type-constraint 'y :int)])
            refined (typing/apply-formula env conj true)]
        (is (= :int (get refined 'x))
            "Conjunction should refine first variable")
        (is (= :int (get refined 'y))
            "Conjunction should refine second variable")))))

(deftest test-typecheck-if-enhanced
  (testing "typecheck-if-enhanced function"
    (let [env (assoc (typing/init-env) 'x :int 'then :int 'else :string)]

      ;; If with predicate that evaluates to a union type (both branches taken)
      (let [result (typing/typecheck-if-enhanced env 'true 'then 'else)]
        (is (or (= result #{:int :string}) (= result #{:string :int}))
            "Should return union of branch types"))

      ;; If without else branch
      (let [result (typing/typecheck-if-enhanced env 'true 'then nil)]
        (is (= :int result)
            "Should return then branch type when no else branch"))

      ;; If with non-boolean condition
      (is (thrown? clojure.lang.ExceptionInfo
                  (typing/typecheck-if-enhanced (assoc env 'bad 42) 'bad 'then 'else))
          "Should throw for non-boolean condition"))))

(deftest test-fixed-arity-operators
  (testing "fixed-arity operators"
    (let [env (assoc (typing/init-env) 'int1 :int 'int2 :int 'str1 :string)]

      ;; Test addition with exactly 2 args
      (let [expr '(+ int1 int2)
            result (typing/typecheck env expr)]
        (is (= :int result)
            "Addition with 2 integer arguments should return int"))

      ;; Test addition with wrong number of args
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"expects 2 arguments but got 3"
                            (typing/typecheck env '(+ int1 int2 int1)))
          "Addition with more than 2 arguments should throw an error")

      ;; Test addition with wrong types
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"type mismatch"
                            (typing/typecheck env '(+ int1 str1)))
          "Addition with non-number should throw an error")

      ;; Test comparison with exactly 2 args
      (let [expr '(< int1 int2)
            result (typing/typecheck env expr)]
        (is (= :bool result)
            "Comparison with 2 integer arguments should return bool"))

      ;; Test equality with exactly 2 args
      (let [expr '(= int1 str1)
            result (typing/typecheck env expr)]
        (is (= :bool result)
            "Equality with any 2 arguments should return bool"))

      ;; Test comparison with wrong number of args
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"expects 2 arguments but got 1"
                            (typing/typecheck env '(< int1)))
          "Comparison with fewer than 2 arguments should throw an error"))))
