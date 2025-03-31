:- module(advanced_occurrence_typing, [
    refine_types/3,
    type_of/3,
    print_env/1,
    print_type/1,
    demo/2
]).

:- use_module(library(ordsets)).

% Basic types
type(any).
type(nil).
type(number).
type(string).
type(boolean).
type(function).
type(atom).

% Type predicates registry
:- dynamic type_predicate/3.

% Register core type predicates
:- assertz(type_predicate(nil_p, X, (X = nil))).
:- assertz(type_predicate(number_p, X, (X = number))).
:- assertz(type_predicate(string_p, X, (X = string))).
:- assertz(type_predicate(boolean_p, X, (X = boolean))).
:- assertz(type_predicate(function_p, X, (X = function))).
:- assertz(type_predicate(atom_p, X, (X = atom))).

% Type constructors
% Union type
union_type(Types, Union) :-
    list_to_ord_set(Types, OrdTypes),
    (OrdTypes = [] -> Union = any;
     OrdTypes = [SingleType] -> Union = SingleType;
     Union = union(OrdTypes)).

% Intersection type
intersection_type(Types, Intersection) :-
    list_to_ord_set(Types, OrdTypes),
    (OrdTypes = [] -> Intersection = nil;
     OrdTypes = [SingleType] -> Intersection = SingleType;
     Intersection = intersection(OrdTypes)).

% Environment operations
% Retrieve type from environment
get_type(Var, Env, Type) :-
    (memberchk(Var:T, Env) -> Type = T; Type = any).

% Update environment with new type
update_env(Var, Type, Env, NewEnv) :-
    delete(Env, Var:_, TempEnv),
    NewEnv = [Var:Type|TempEnv].

% Remove a type from a union
remove_from_union(union(Types), TypeToRemove, Result) :-
    ord_del_element(Types, TypeToRemove, NewTypes),
    union_type(NewTypes, Result).
remove_from_union(Type, Type, nil) :- !.
remove_from_union(Type, _, Type).

% Apply type predicates to refine types
% Each predicate maps directly to a specific type
apply_predicate(nil_p, _, pos, nil) :- !.
apply_predicate(number_p, _, pos, number) :- !.
apply_predicate(string_p, _, pos, string) :- !.
apply_predicate(boolean_p, _, pos, boolean) :- !.
apply_predicate(function_p, _, pos, function) :- !.
apply_predicate(atom_p, _, pos, atom) :- !.
apply_predicate(even_p, Type, pos, number) :- !. % Even numbers are numbers

% Negative case handling
apply_predicate(nil_p, Type, neg, NegType) :-
    (Type = union(Types) -> 
        ord_del_element(Types, nil, NewTypes),
        union_type(NewTypes, NegType);
     Type = nil -> NegType = any;
     NegType = Type).

apply_predicate(number_p, Type, neg, NegType) :-
    (Type = union(Types) -> 
        ord_del_element(Types, number, NewTypes),
        union_type(NewTypes, NegType);
     Type = number -> NegType = any;
     NegType = Type).

apply_predicate(string_p, Type, neg, NegType) :-
    (Type = union(Types) -> 
        ord_del_element(Types, string, NewTypes),
        union_type(NewTypes, NegType);
     Type = string -> NegType = any;
     NegType = Type).

apply_predicate(boolean_p, Type, neg, NegType) :-
    (Type = union(Types) -> 
        ord_del_element(Types, boolean, NewTypes),
        union_type(NewTypes, NegType);
     Type = boolean -> NegType = any;
     NegType = Type).

apply_predicate(function_p, Type, neg, NegType) :-
    (Type = union(Types) -> 
        ord_del_element(Types, function, NewTypes),
        union_type(NewTypes, NegType);
     Type = function -> NegType = any;
     NegType = Type).

apply_predicate(atom_p, Type, neg, NegType) :-
    (Type = union(Types) -> 
        ord_del_element(Types, atom, NewTypes),
        union_type(NewTypes, NegType);
     Type = atom -> NegType = any;
     NegType = Type).

apply_predicate(even_p, Type, neg, NegType) :-
    % For negation, same as number_p
    (Type = union(Types) -> 
        ord_del_element(Types, number, NewTypes),
        union_type(NewTypes, NegType);
     Type = number -> NegType = any;
     NegType = Type).

% Merge environments (for disjunctions)
merge_envs(Env1, Env2, MergedEnv) :-
    merge_env_vars(Env1, Env2, VarTypes),
    pairs_to_env(VarTypes, MergedEnv).

% Create list of Var-Type pairs from both environments
merge_env_vars([], [], []).
merge_env_vars([Var:Type1|Env1], Env2, [Var-MergedType|Rest]) :-
    (select(Var:Type2, Env2, RestEnv2) ->
        union_type([Type1, Type2], MergedType),
        merge_env_vars(Env1, RestEnv2, Rest)
    ;
        MergedType = Type1,
        merge_env_vars(Env1, Env2, Rest)
    ).
merge_env_vars([], [Var:Type|Env2], [Var-Type|Rest]) :-
    merge_env_vars([], Env2, Rest).

% Convert list of Var-Type pairs to environment
pairs_to_env([], []).
pairs_to_env([Var-Type|Rest], [Var:Type|EnvRest]) :-
    pairs_to_env(Rest, EnvRest).

% Intersect environments (for conjunctions)
intersect_envs(Env1, Env2, IntersectedEnv) :-
    intersect_env_vars(Env1, Env2, VarTypes),
    pairs_to_env(VarTypes, IntersectedEnv).

% Create list of Var-Type pairs with intersected types
intersect_env_vars([], [], []).
intersect_env_vars([Var:Type1|Env1], Env2, [Var-IntersectedType|Rest]) :-
    (select(Var:Type2, Env2, RestEnv2) ->
        intersection_type([Type1, Type2], IntersectedType),
        intersect_env_vars(Env1, RestEnv2, Rest)
    ;
        IntersectedType = Type1,
        intersect_env_vars(Env1, Env2, Rest)
    ).
intersect_env_vars([], [Var:Type|Env2], [Var-Type|Rest]) :-
    intersect_env_vars([], Env2, Rest).

% Process expressions - core of occurrence typing
% Basic predicate application
process_expr(pred(Pred, Var), Env, PosEnv, NegEnv) :-
    get_type(Var, Env, VarType),
    % Directly call apply_predicate without using type_predicate lookup
    apply_predicate(Pred, VarType, pos, PosType),
    apply_predicate(Pred, VarType, neg, NegType),
    update_env(Var, PosType, Env, PosEnv),
    update_env(Var, NegType, Env, NegEnv).

% Negation
process_expr(not(Expr), Env, PosEnv, NegEnv) :-
    process_expr(Expr, Env, SubPosEnv, SubNegEnv),
    PosEnv = SubNegEnv,
    NegEnv = SubPosEnv.

% Conjunction (AND)
process_expr(and(Expr1, Expr2), Env, PosEnv, NegEnv) :-
    % Process first expression
    process_expr(Expr1, Env, PosEnv1, NegEnv1),
    
    % Process second expression in the positive environment from first
    process_expr(Expr2, PosEnv1, PosEnv, _),
    
    % For the negative environment:
    % If first expr is false, AND is false regardless of second
    % If first expr is true but second is false, AND is false
    % So we use the negative environment from first expr
    NegEnv = NegEnv1.

% Disjunction (OR)
process_expr(or(Expr1, Expr2), Env, PosEnv, NegEnv) :-
    process_expr(Expr1, Env, PosEnv1, NegEnv1),
    process_expr(Expr2, NegEnv1, PosEnv2, NegEnv2),
    merge_envs(PosEnv1, PosEnv2, PosEnv),
    NegEnv = NegEnv2.

% Conditional (IF)
process_expr(if(Test, Then, Else), Env, PosEnv, NegEnv) :-
    process_expr(Test, Env, ThenEnv, ElseEnv),
    process_expr(Then, ThenEnv, ThenPosEnv, ThenNegEnv),
    process_expr(Else, ElseEnv, ElsePosEnv, ElseNegEnv),
    merge_envs(ThenPosEnv, ElsePosEnv, PosEnv),
    merge_envs(ThenNegEnv, ElseNegEnv, NegEnv).

% Nested arbitrary expressions
process_expr(complex(Exprs), Env, PosEnv, NegEnv) :-
    process_complex_expr(Exprs, Env, PosEnv, NegEnv).

% Process a list of expressions sequentially
process_complex_expr([], Env, Env, Env).
process_complex_expr([Expr|Rest], Env, FinalPosEnv, FinalNegEnv) :-
    process_expr(Expr, Env, PosEnv, NegEnv),
    process_complex_expr(Rest, PosEnv, FinalPosEnv, FinalNegEnv).

% Main API predicate
refine_types(Expr, InitialEnv, Result) :-
    process_expr(Expr, InitialEnv, PosEnv, NegEnv),
    Result = result(pos_env(PosEnv), neg_env(NegEnv)).

% Type checking
type_of(Expr, Env, Type) :-
    refine_types(Expr, Env, result(pos_env(PosEnv), _)),
    get_type(Expr, PosEnv, Type).

% Pretty printing
print_type(any) :- write('any'), !.
print_type(nil) :- write('nil'), !.
print_type(number) :- write('number'), !.
print_type(string) :- write('string'), !.
print_type(boolean) :- write('boolean'), !.
print_type(function) :- write('function'), !.
print_type(atom) :- write('atom'), !.
print_type(union(Types)) :-
    write('Union['),
    print_type_list(Types),
    write(']'), !.
print_type(intersection(Types)) :-
    write('Intersection['),
    print_type_list(Types),
    write(']'), !.
print_type(Other) :- write(Other).

print_type_list([]).
print_type_list([Type]) :- print_type(Type), !.
print_type_list([Type|Rest]) :-
    print_type(Type),
    write(', '),
    print_type_list(Rest).

print_env([]).
print_env([Var:Type|Rest]) :-
    write('  '),
    write(Var),
    write(': '),
    print_type(Type),
    nl,
    print_env(Rest).

% Demo function
demo(Expr, Env) :-
    refine_types(Expr, Env, Result),
    write('Initial environment:'), nl,
    print_env(Env), nl,
    write('Expression: '), write(Expr), nl, nl,
    write('Positive branch environment:'), nl,
    Result = result(pos_env(PosEnv), neg_env(NegEnv)),
    print_env(PosEnv), nl,
    write('Negative branch environment:'), nl,
    print_env(NegEnv), nl.

% Custom type predicates can be added dynamically:
% ?- assertz(type_predicate(even_p, number, (X mod 2 =:= 0))).

% Example usage:
% ?- demo(pred(number_p, x), [x:any]).
% 
% ?- demo(and(pred(number_p, x), not(pred(nil_p, x))), [x:any]).
% 
% ?- demo(or(pred(number_p, x), pred(string_p, x)), [x:any]).
% 
% ?- demo(and(not(pred(nil_p, x)), or(pred(number_p, x), pred(string_p, x))), [x:any]).
% 
% ?- demo(complex([pred(number_p, x), if(pred(number_p, y), pred(string_p, z), pred(boolean_p, z))]), [x:any, y:any, z:any]). 