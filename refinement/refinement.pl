:- module(refinement, [
              refine/4,
              predicate_type/2,
              convert_env_to_dnf/2
          ]).

:- use_module(dnf, [
                  construct/2,
                  make_union/2,
                  make_inter/2,
                  make_neg/2,
                  normalize/2,
                  basic_type/1
              ]).
:- use_module(dnf_readable, [dnf_to_readable/2]).


predicate_type(number_p,   number).
predicate_type(integer_p,  integer).
predicate_type(float_p,    float).
predicate_type(rational_p, rational).
predicate_type(integer_p,  integer).
predicate_type(string_p,   string).
predicate_type(list_p,     list).

refine(PredExpr, InitialEnv, TrueEnv, FalseEnv) :-
    PredExpr =.. [PredName, Var],
    atom(Var),
    predicate_type(PredName, PredTypeExpr),
    !,
    get_type(Var, InitialEnv, VarDNF),
    dnf:normalize(PredTypeExpr, PredicateDNF),

    dnf:make_inter([VarDNF, PredicateDNF], TrueDNF),
    dnf:make_neg(PredTypeExpr, NegPredicateDNF),
    dnf:make_inter([VarDNF, NegPredicateDNF], FalseDNF),


    % Create output environments
    put_dict(Var, InitialEnv, TrueDNF, TrueEnv),
    put_dict(Var, InitialEnv, FalseDNF, FalseEnv).

refine(not(SubExpr), InitialEnv, TrueEnv, FalseEnv) :- !,
    refine(SubExpr, InitialEnv, FalseEnv, TrueEnv).

refine(and(ExprA, ExprB), InitialEnv, TrueEnv, FalseEnv) :- !,
    refine(ExprA, InitialEnv, EnvA_True, EnvA_False),
    refine(ExprB, EnvA_True, TrueEnv, EnvB_False),
    merge(dnf:make_union, EnvA_False, EnvB_False, FalseEnv).

refine(or(ExprA, ExprB), InitialEnv, TrueEnv, FalseEnv) :- !,
    refine(ExprA, InitialEnv, EnvA_True, EnvA_False),
    refine(ExprB, InitialEnv, EnvB_True, EnvB_False),
    merge(dnf:make_union, EnvA_True, EnvB_True, TrueEnv),
    merge(dnf:make_inter, EnvA_False, EnvB_False, FalseEnv).

get_var_representation(Var, MixedEnvDict, Representation) :-
    ( get_dict(Var, MixedEnvDict, Representation) ->
      true
    ; dnf:normalize(any, Representation)).

merge(Operator, EnvA, EnvB, Merged) :-
    dict_keys(EnvA, KeysA),
    dict_keys(EnvB, KeysB),
    ord_union(KeysA, KeysB, AllVars),
    foldl(merge_var_type(Operator, EnvA, EnvB), AllVars, _{}, Merged).

merge_var_type(Operator, EnvA, EnvB, Var, EnvAcc, EnvNext) :-
    get_type(Var, EnvA, DNFA),
    get_type(Var, EnvB, DNFB),
    call(Operator, [DNFA, DNFB], MergedDNF),
    put_dict(Var, EnvAcc, MergedDNF, EnvNext).

get_type(Var, Env, DNFType) :-
    (get_dict(Var, Env, DNFType) -> true
    ; dnf:construct(any, DNFType)).

convert_env_to_dnf(ReadableEnvList, MixedEnvDict) :-
    is_list(ReadableEnvList), !,
    foldl(convert_env_pair, ReadableEnvList, _{}, MixedEnvDict).
convert_env_to_dnf(DictIn, _DictOut) :-
    throw(error(type_error(list, DictIn), convert_env_to_dnf/2)).

convert_env_pair(Var:InputRepr, DictAcc, DictNext) :-
    atom(Var),
    ( ground(InputRepr),
      \+ is_type_constructor(InputRepr) ->
      Representation = value(InputRepr)
    ; dnf:normalize(InputRepr, Representation)),
    put_dict(Var, DictAcc, Representation, DictNext).

is_type_constructor(Term) :-
    compound(Term),
    ( functor(Term, union, _)
    ; functor(Term, inter, _)
    ; functor(Term, neg, _)
    ), !.
is_type_constructor(Term) :-
    atom(Term),
    dnf:basic_type(Term).
