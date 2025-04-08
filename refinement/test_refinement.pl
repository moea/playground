:- module(test_refinement, []).

:- use_module(library(plunit)).
:- use_module(refinement).
:- use_module(dnf, [construct/2]). % For defining types in tests
:- use_module(dnf_readable, [dnf_to_readable/2]). % For checking results

test_refinement(Expression, InitialReadableEnvList, ExpectedTrue, ExpectedFalse) :-
    refinement:convert_env_to_dnf(InitialReadableEnvList, DNFEnv),
    refinement:refine(Expression, DNFEnv, TrueEnv, FalseEnv),
    check_envs(TrueEnv, FalseEnv, ExpectedTrue, ExpectedFalse).

check_envs(TrueDNFEnv, FalseDNFEnv, ExpectedTrue, ExpectedFalse) :-
    compare_env_readable(TrueDNFEnv, ExpectedTrue),
    compare_env_readable(FalseDNFEnv, ExpectedFalse).

compare_env_readable(ActualDNFEnv, ExpectedList) :-
    dict_pairs(ActualDNFEnv, _, ActualPairsList),
    sort(ActualPairsList, SortedActualPairs),

    findall(Var-ExpectedType, member(Var:ExpectedType, ExpectedList), ExpectedPairs),
    sort(ExpectedPairs, SortedExpectedPairs),

    maplist(pair_dnf_to_readable, SortedActualPairs, ActuaReadablePairs), %
    sort(ActuaReadablePairs, SortedActualReadablePairs),

    ( SortedActualReadablePairs == SortedExpectedPairs ->
      true
    ;   format(atom(Msg), 'Environment mismatch:~n  Expected Readable: ~w~n  Actual Readable:   ~w~n  Actual DNF Env:    ~w',
               [SortedExpectedPairs, SortedActualReadablePairs, ActualDNFEnv]),
        write(user_error, Msg), nl(user_error),
        assertion(fail)
    ).

pair_dnf_to_readable(Var-ActualDNF, Var-ActualReadable) :-
    dnf_to_readable(ActualDNF, ActualReadable).

:- begin_tests(refinement).


test(predicate_simple) :-
    test_refinement(
        integer_p(x),
        [x: number],
        [x: integer],
        [x: inter([number, neg(integer)])]).

test(predicate_no_refine) :-
    test_refinement(
        string_p(x),
        [x: number],
        [x: nil],
        [x: number]).

test(negation) :-
    test_refinement(
        not(integer_p(x)),
        [x: number],
        [x: inter([number, neg(integer)])],
        [x: integer]).

test(and_simple) :-
    test_refinement(
        and(number_p(x), not(string_p(x))),
        [x: any],
        [x: number],
        [x: neg(number)]).

test(and_sequential) :-
    test_refinement(
        and(number_p(x), integer_p(x)),
        [x: any],
        [x: integer],
        [x: union([inter([number, neg(integer)]), neg(number)])]).

test(or_simple) :-
    test_refinement(
        or(integer_p(x), string_p(x)),
        [x: any],
        [x: union([integer, string])],
        [x: inter([neg(integer), neg(string)])]).

test(or_overlapping) :-
    test_refinement(
        or(number_p(x), integer_p(x)),
        [x: any],
        [x: number],
        [x: neg(number)]).

test(multi_var) :-
    test_refinement(
        and(number_p(x), string_p(y)),
        [x: any, y: any],
        [x: number, y: string],
        [x: any, y: any]).

test(complex_nested) :-
    test_refinement(
        or(and(number_p(x), not(integer_p(x))), and(integer_p(x), not(number_p(x)))),
        [x: any],
        [x: inter([number, neg(integer)])],
        [x: union([integer, neg(number)])]).

test(union_predicate_intersect) :-
    test_refinement(
        integer_p(x),
        [x: union([integer, string])],
        [x: integer],
        [x: string]).

test(union_predicate_partial_intersect) :-
    test_refinement(
        integer_p(x),
        [x: union([number, string])],
        [x: integer],
        [x: union([string, inter([number, neg(integer)])])]).

test(union_predicate_no_intersect) :-
    test_refinement(
        integer_p(x),
        [x: union([float, string])],
        [x: nil],
        [x: union([float, string])]).

test(union_negation) :-
    test_refinement(
        not(integer_p(x)),
        [x: union([integer, string])],
        [x: string],
        [x: integer]).

test(union_and) :-
    test_refinement(
        and(number_p(x), not(integer_p(x))),
        [x: union([number, string])],
        [x: inter([number, neg(integer)])],
        [x: union([integer, string])]).

test(nested_and_or_multi_var) :-
    test_refinement(
        and(or(integer_p(x), string_p(x)), or(number_p(y), list_p(y))),
        [x: any, y: any],
        [x: union([integer, string]),
         y: union([list, number])],
        [x: union([integer, string, inter([neg(integer), neg(string)])]),
         y: any ]).

test(nested_neg_and_or) :-
    test_refinement(
        not(or(and(number_p(x), integer_p(x)), string_p(y))),
        [x: any, y: any],
        [x: union([inter([number, neg(integer)]), neg(number)]),
         y: neg(string)],
        [x: any, y: any]).

test(deeper_nesting_same_var) :-
    test_refinement(
        and(number_p(x), or(not(integer_p(x)), not(number_p(x)))),
        [x: any],
        [x: inter([number, neg(integer)])],
        [x: union([integer, neg(number)])]).

:- end_tests(refinement).
