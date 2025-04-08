:- module(dnf, [
              make_union/2,
              make_inter/2,
              make_neg/2,
              normalize/2,
              dnf_subtype_of/2,
              subtype_of/2,
              construct/2,
              basic_type/1
          ]).

basic_type(any).
basic_type(nil).
basic_type(number).
basic_type(integer).
basic_type(float).
basic_type(list).
basic_type(string).
basic_type(rational).

concrete(Type) :-
    basic_type(Type),
    Type \== any,
    Type \== nil.

subtype_of(integer, number).
subtype_of(float, number).
subtype_of(rational, number).

subtype_of(neg(Super), neg(Sub)) :-
    Super \== Sub,
    subtype_of(Sub, Super).

subtype_of(nil, _).
subtype_of(_, any).

subtype_of(Sub, Super) :- Sub == Super.

make_union(Types, DNF) :- normalize(union(Types), DNF).
make_inter(Types, DNF) :- normalize(inter(Types), DNF).
make_neg(Type,    DNF) :- normalize(neg(Type),    DNF).

construct(union(Args), DNF) :- !, make_union(Args, DNF).
construct(inter(Args), DNF) :- !, make_inter(Args, DNF).
construct(neg(Arg),    DNF) :- !, make_neg(Arg, DNF).
construct(Term, DNF) :-
    normalize(Term, DNF).

normalize(any, union([inter([])])) :- !.
normalize(nil, union([])) :- !.

normalize(neg(Type), DNF) :- !,
    normalize_neg(Type, DNF).

normalize(union(Types), DNF) :- !,
    maplist(normalize, Types, DNFs),
    flatten_unions(DNFs, Flattened),
    simplify(union(Flattened), DNF).

normalize(inter(Types), DNF) :- !,
    maplist(normalize, Types, DNFs),
    distribute(DNFs, DistributedDNF),
    simplify(DistributedDNF, DNF).

normalize(Type, union([inter([Type])])) :-
    concrete(Type),
    !.

normalize_neg(any, union([])) :- !.
normalize_neg(nil, union([inter([])])) :- !.
normalize_neg(Type, union([inter([neg(Type)])])) :-
    concrete(Type),  !.
normalize_neg(neg(Type), DNF) :- !,
    normalize(Type, DNF).
normalize_neg(union(Types), DNF) :- !,
    maplist(negate, Types, NegatedTerms),
    normalize(inter(NegatedTerms), DNF).
normalize_neg(inter(Types), DNF) :- !,
    maplist(negate, Types, NegatedTerms),
    normalize(union(NegatedTerms), DNF).

flatten_unions(Unions, Members) :-
    foldl(flatten_union_acc, Unions, [], Members).

flatten_union_acc(union(Members), AccMembers, AccOutMembers) :-
    ord_union(AccMembers, Members, AccOutMembers).
flatten_union_acc(nil, AccMembers, AccMembers).

distribute([DNF|DNFs], ResultDNF) :-
    foldl(distribute_acc, DNFs, DNF, ResultDNF).
distribute([], union([inter([])])).


distribute_acc(union(IntersA), union(IntersB), union(IntersOut)) :-
    findall(inter(CombinedLits),
            (member(inter(LitsA), IntersA),
             member(inter(LitsB), IntersB),
             append(LitsA, LitsB, CombinedLits)),
            ResultInters),
    list_to_ord_set(ResultInters, IntersOut).


canonicalize(union([]), nil) :- !.
canonicalize(Union, Union) :- Union = union(_).

simplify(union(Inters), SimplifiedDNF) :-
    maplist(simplify_inter, Inters, SimplifiedInters),
    include(\=(nil), SimplifiedInters, NonNilInters),
    list_to_ord_set(NonNilInters, UniqueInters),
    ( has_complementary_inter(UniqueInters) ->
      SimplifiedDNF = union([inter([])])
    ;
    absorb(UniqueInters, MinimalInters),
    canonicalize(union(MinimalInters), SimplifiedDNF)).

has_complementary_inter(Inters) :-
    member(inter([T]), Inters),
    concrete(T),
    memberchk(inter([neg(T)]), Inters).

absorb(Inters, IntersOut) :-
    findall(InterA,
            (member(InterA, Inters),
             member(InterB, Inters),
             InterA \== InterB,
             inter_subtype_of(InterA, InterB)),
            AbsorbedInters),
    ord_subtract(Inters, AbsorbedInters, IntersOut).

inter_subtype_of(inter(LitsA), inter(LitsB)) :-
    forall(member(LitB, LitsB),
           (member(LitA, LitsA), subtype_of(LitA, LitB))).

simplify_inter(inter(Literals), Inter) :-
    ( list_to_ord_set(Literals, Lits),
      ( contradictory(Lits)      -> Inter = nil
      ; disjoint_concretes(Lits) -> Inter = nil
      ; simplify_lits(Lits, Inter))).

simplify_lits(LitsIn, Inter) :-
    join_negs(LitsIn, Intermediate),
    subsume_lits(Intermediate, Minimal),
    Inter = inter(Minimal).

join_negs(Lits, LitsOut) :-
    findall(neg(TB),
            (member(neg(TB), Lits),
             concrete(TB),
             member(TA, Lits),
             concrete(TA),
             are_disjoint(TA, TB)),
            RedundantNegs),
    ord_subtract(Lits, RedundantNegs, LitsOut).

subsume_lits(Lits, LitsOut) :-
    findall(LitToRemove,
            (member(LitToRemove, Lits),
             subsumed_in(LitToRemove, Lits)
            ),
            LitsToRemove),
    ord_subtract(Lits, LitsToRemove, LitsOut).

subsumed_in(LitA, Lits) :- %
    member(LitB, Lits),
    LitA \== LitB,
    subtype_of(LitB, LitA),
    !.

contradictory([Lit|Lits]) :-
    ( negated_in(Lit, Lits) -> true
    ; contradictory(Lits)).
contradictory([]) :- fail.

negated_in(neg(TA), Ord) :- !,
    member(TB, Ord), TA \== TB, subtype_of(TB, TA).
negated_in(Lit, Ord) :-
    negate(Lit, Negation), ord_memberchk(Negation, Ord), !.
negated_in(TA, Ord) :-
    member(neg(TB), Ord), TA \== TB, subtype_of(TA, TB).

negate(neg(T), T).
negate(T, neg(T)).

disjoint_concretes(Literals) :-
    findall(T, (member(T, Literals), concrete(T)), BasicTypes),
    member(TA, BasicTypes),
    member(TB, BasicTypes),
    TA @< TB,
    are_disjoint(TA, TB).

are_disjoint(TA, TB) :-
    concrete(TA),
    concrete(TB),

    ( disjoint_types(TA, TB)
    ; disjoint_types(TB, TA)

    ; subtype_of(TA, SuperA), SuperA \== TA,
      ( disjoint_types(SuperA, TB)
      ; are_disjoint(SuperA, TB))

    ; subtype_of(TB, SuperB), SuperB \== TB,
      ( disjoint_types(SuperB, TA)
      ; are_disjoint(SuperB, TA))).

disjoint_types(number,  string).
disjoint_types(integer, float).
disjoint_types(float,   rational).
disjoint_types(list,    number).
disjoint_types(list,    string).

dnf_subtype_of(nil, _).

dnf_subtype_of(union(IntersA), union(IntersB)) :-
    forall(member(InterA, IntersA) ,
           has_subtype_inter(InterA, IntersB)).

has_subtype_inter(inter(LitsA), IntersB) :-
    member(inter(LitsB), IntersB),
    forall(member(LitB, LitsB) ,
           (member(LitA, LitsA), subtype_of(LitA, LitB))).
