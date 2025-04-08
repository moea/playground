:- module(dnf_readable, [
              dnf_to_readable/2
          ]).

dnf_to_readable(nil, nil) :- !.
dnf_to_readable(union([]), nil) :- !.

dnf_to_readable(union([inter([])]), any) :- !.

dnf_to_readable(union([Inter]), ReadableInter) :- !,
    simplify_inter(Inter, ReadableInter).

dnf_to_readable(union(Inters), ReadableUnion) :-
    Inters = [_,_|_], !,
    maplist(simplify_inter, Inters, SimplifiedMembersRaw),

    ( member(any, SimplifiedMembersRaw) ->
      ReadableUnion = any
    ;
    delete(SimplifiedMembersRaw, nil, SimplifiedMembers),
    ( SimplifiedMembers == [] ->
      ReadableUnion = nil
    ; SimplifiedMembers = [SingleMember] ->
      ReadableUnion = SingleMember
    ;
    ( forall(member(M, SimplifiedMembers), is_literal(M)) ->
      sort(SimplifiedMembers, SortedMembers),
      ReadableUnion = union(SortedMembers)
    ;
    sort(SimplifiedMembers, SortedMembers),
    ReadableUnion = union(SortedMembers)))).

simplify_inter(inter([]), any) :- !.

simplify_inter(inter([Lit]), Lit) :- !,
    is_literal(Lit).

simplify_inter(inter(Lits), inter(SortedLits)) :-
    Lits = [_,_|_], !,
    sort(Lits, SortedLits).

is_literal(neg(T)) :- atomic(T), !.
is_literal(Term)   :- atomic(Term), !.
