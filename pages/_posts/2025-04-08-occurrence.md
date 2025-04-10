---
layout: post
title:  "Flow Typing, Prolog & Normal Forms"
date:   2025-04-08 04:00:00 +0000
categories: prolog logic flow typing
author: Moe Aboulkheir
---

_Occurrence typing_ (per [Typed
Racket](https://docs.racket-lang.org/ts-guide/)) or _type narrowing_
([Typescript](https://www.typescriptlang.org/)[^1]) are different names
for what's generally called _flow-sensitive typing_, or _flow typing_,
a static analysis technique.  Types are _refined_ in response to a
program's statically analyzed control flow[^2]
--- allowing for more precise type information within conditional
statements.  The predicates/operators often provide type information
about the variables used in the branches.  A simple example of flow
typing for the [Python](https://python.org) programmers:

```python
def f(x: str | int) -> str | int:
    if isinstance(x, int):
        return x + 1
    else:
        return x + "1"
```

[mypy](https://mypy-lang.org/) is totally fine with this --- refining
the type of `x` in each branch, to `int` and `str` respectively.
Nothing fancy.  Like most things, it's a harder problem than it looks.

The goal of this article is to narrate the implementation of a _minimal_
flow-sensitive typechecker for a trivial DSL to a reader not
necessarily intimate with
[Prolog](https://en.wikipedia.org/wiki/Prolog), written by an author
with very limited experience with same.  It is as much about type
representations as it about Prolog and flow-sensitive typechecking ---
I've tried to make the potentially boring parts easy to skip.  To give
you an idea of where we'll end up, our basic refinement system will
allow us to write tests like this:

```prolog
test(deeper_nesting_same_var) :-
    test_refinement(
        and(number_p(x), or(not(integer_p(x)), not(number_p(x)))), % if
        [ x: any ], % env
        [ x: inter([number, neg(integer)]) ], % then
        [ x: union([integer, neg(number)]) ]  % else
    ).
```

## Prolog :-

A language so unpopular that [_Larry
Wall_](https://en.wikipedia.org/wiki/Larry_Wall) mogged its file
extension out of existence decades ago. I'm going to assume the reader
has heard vague murmurs about Prolog but can't necessarily read it ---
though knows of its more
distinguishing features, principally
[backtracking](https://en.wikipedia.org/wiki/Backtracking) and
[unification](https://en.wikipedia.org/wiki/Unification_(computer_science)).

This was my situation last week. I'd read a couple of
books about expert systems --- light on detail --- way back in the
[AltaVista](https://en.wikipedia.org/wiki/AltaVista)[^3] days, when that's what was in the library under _Artificial
Intelligence_.  All I really retained was that this stuff was being
used for cardiac triage in the late '70s, and that the [`cut` operator](https://homepage.divms.uiowa.edu/~hzhang/c188/notes/ch08b-cut.pdf) is
politically sensitive within the Prolog community[^4].  Having implemented
a couple of type inference algorithms recently, I thought I'd try
tackling a type problem (though not inferential) in a language where
unification is the principal means through which information propagates through
programs.

Given that I've been programming in Prolog after-hours for all of a
week, feel free to take the idiomaticity of my implementation and the
terminological precision of my exegesis with a grain of salt, though
I've endeavoured to be careful.  I even joined `#prolog` on
[freenode](https://en.wikipedia.org/wiki/Freenode) to ask about some
cultural stuff, but there was nobody there.  I haven'tf used IRC in 15
years --- I was certain the Prolog cranks[^5] would be all over it.
Should've tried Usenet.

## Type Representation

Our type system supports supports unions, intersections and
complements (though I'll use the term _negation_, for extra confusion,
because it's easier to abbreviate).  If we're reasoning about types
with complex shapes, we'd benefit from a canonical representation into
which we can simplify terms.  Then we can throw any garbage we want at
our machinery, and hopefully get back something consistent, which we
can simply test for subtyping and efficiently test for equality.

[Binary Decision
Diagrams](https://www.wikiwand.com/en/articles/Binary_decision_diagram)
are an obvious, powerful canonical representation --- they're used
internally by some other set-theoretic type systems[^6].  That said,
there is no practical BDD library for
[SWI-Prolog](https://www.swi-prolog.org/), and we're not going to
build one in for this post.  And, subtyping is awkward with BDDs and
involves making complex trade-offs, it seems from a distance.  I'm no
expert.  Maybe something to explore in a future post.

I went with [Disjunctive Normal
Form](https://en.wikipedia.org/wiki/Disjunctive_normal_form) --- it's
simple to implement, and subtyping is elegant --- _beautiful_, even.
But does have its shortcomings, which I'll discuss at the end of the
article.  For those not completely into this horseshit, BDD and DNF
are both representations of logical formulas, or, if you prefer,
boolean functions.  Because of the correspondence between
set-theoretic operations and those of boolean algebra --- if we think
of types as sets of values, we can see why it might make sense to
encode them as boolean functions.  This is in contrast to thinking
about types _purely_ algebraically, per my previous post:
[Typechecking GADTs in
Clojure](http://localhost:4000/playground/clojure/gadt/static/typing/2025/03/29/gadt.html).

In any case, you're not going to have to know very much about the
representation, if you don't already, because we'll have predicates
which convert from programmer-canonical type representations and DNF,
and it's not _that_ hard to read.  In short, it's a _sum of products_
form, which is to say, it consists of disjunctions of conjunctions
(unions types of intersection types), with the latter comprised of
literals (symbolic type names, in our case) or their negations
(negated, or complement types).  A term can simplify to a (possibly
negated) literal.

## The Little Type System That Could

Our type lattice has `any` at the top, `nil` at the bottom, and
disjoint `number` and `string` types.  `number` has three subtypes,
`integer`, `rational` and `float`, where `integer`/`rational` are
disjoint from `float`, but overlap themselves.

### Implementation

I'll go through some of the high-level stuff, as a way of introducing
some Prolog, and talk through the rudimentary simpiflications which
are performed as part of the DNF conversion process.  If you're still
awake by the end, we can talk about type refinement When we get to the
dull bit, I'll give you a link to skip over it.  If you **already know
Prolog** [click here](#literals).


```prolog
:- module(dnf, [...]).

basic_type(any).
basic_type(nil).
basic_type(number).
basic_type(integer).
basic_type(float).
basic_type(string).
basic_type(rational).
```

These statements are _facts_.  In Prolog we have facts, and _rules_,
which are both predicates  Atoms (lower cased/underscored names,
for the most part) evaluate to themselves, and are like symbols in
Lisp.  `any` and `nil` etc. are just symbolic values, they have no
semantics.  Variables are uppercased.  Here's an example of us
interacting with `basic_type` via the
[REPL](https://en.wikipedia.org/wiki/Read%E2%80%93eval%E2%80%93print_loop)
(or "interactive language shell"):

```prolog
?- basic_type(any).
true.
?- basic_type([oysters, clams]).
false.
?- basic_type(X).
X = any ;
X = nil ;
X = number ;
...
```

In the last case, where `X` is a fresh variable, we're effectively
treating the predicate like a relation.  I'm hitting `<TAB>` to get
the next value.  Now, for a rule:

```prolog
concrete(Type) :-
    basic_type(Type),
    Type \== any,
    Type \== nil.
```

This a [Horn clause](https://en.wikipedia.org/wiki/Horn_clause): the
_head_ of the rule is everything before the _implies_, or `:-`, its
body consists of a _goal_.  This rule has three subgoals, joined by
the logical conjunction operator, comma.  All of these subgoals must
succeed for `concrete_type` to succeed.

```prolog
subtype_of(integer, number).
subtype_of(float,   number).
subtype_of(rational, number).

subtype_of(neg(Super), neg(Sub)) :-
    Super \== Sub,
    subtype_of(Sub, Super).

subtype_of(nil, _).
subtype_of(_, any).

subtype_of(Sub, Super) :- Sub == Super.
```

There'll be a separate subtyping predicate for DNF, but the compound
terms will contain these type atoms as literals --- `integer`,
`rational`, etc. --- so this is where we ground our subtyping
relation.  What looks like a predicate invocation in the argument
positions for the negated type case (which you'll notice is
[contravariant](https://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)))
is pattern-matching.

Prolog allows compound expressions (_compounds_) in the predicate
invocation shape to be used to structure data, with arbitrary nesting,
when passed or used as arguments.  Confusingly, these non-predicates
are called _functors_.  Let's get a feel for why we used Prolog in the
first place:

```prolog
disjoint_types(number,  string).
disjoint_types(integer, float).
disjoint_types(float,   rational).

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
```

The semicolons are left-justified, and separate subgoals into
disjunctions.  I've tried to make the groupings as clear as possible
--- it's no fun turning everything into its own predicate (which you
have to do a lot of the time[^7]).  So here, we're saying quite a bit:
 - Both types must be concrete.
 - Pairwise, both types can have been explicitly declared as disjoint:
   - or, there exists _some_ supertype of `TA` which is not `TA` and is either explicitly or transitively (via recursion) disjoint from `TB`.
   - or, the same for the `TB`/`TA` pairing.

`SuperA` and `SuperB` are fresh variables, which'll be instantiated
with every supertype of `TA` and then `TB` until one of subgoals are
satisfied or the queries are exhausted.  Obviously we won't get the
final subgoal if the second subgoal is satisfied. Fun!

<a id="literals"></a>
### DNF Literals

Below are some examples of how we represent DNF literals within our
program., so we know what we're dealing with.  `construct` takes a
human-readable type representation and a variable, which it unifies
with the simplified DNF:

```prolog
?- construct(union([float, rational]), A).
A = union([inter([float]), inter([rational])]).

?- construct(union([integer, neg(integer)]), B).
B = union([inter([])]).. % any, the top type, the big boy

?- construct(inter([integer, neg(integer)]), C).
C = union([]) % nil, the uninhabited type

?- construct(union([inter([neg(float),
                           neg(integer)]), string]), D).
D = union([inter([string]),
           inter([neg(float),
                  neg(integer)])]).
```

I wasn't kidding when I said DNF is a disjunction of conjunctions ---
there is only ever one `union` (the outermost form), and it must
_only_ contain intersections.  The structure is never deeper than
`union` -> `inter` -> `literal`.  If you squint, you can see how the
representations are equivalent.

Let's look at how we handle subtyping in DNF, given our atomic
subtyping implementation above.

```prolog
dnf_subtype_of(union(IntersA), union(IntersB)) :-
    forall(member(InterA, IntersA) ,
           has_subtype_inter(InterA, IntersB)).

has_subtype_inter(inter(LitsA), IntersB) :-
    member(inter(LitsB), IntersB),
    forall(member(LitB, LitsB) ,
           (member(LitA, LitsA), subtype_of(LitA, LitB))).
```

That's all there is!  Across the two predicates, we're declaring:
 - For _all_ intersections `IntersA` in the first union, destructure its constituent literals as `LitsA`, in turn:
   - For _some_ intersection contaning literals `LitsB`, from the second union:
     - Is it the case that _every_ member of `LitsB` has a subtype literal in `LitsA`?

`<a id="construction"></a>
### DNF Construction

You may find this section boring.  If you're only interested in the
_goods_, the white Bronco, the _big show_ --- [**jump straight to type
refinement**](#refinement), although this'll provide a helpful, if
verbose, foundation --- that system can only function because the
properties we establish here.  If you already understand DNF, just
skip it.

Anyway, let's talk through what happens if we construct:

```prolog
union([number, string, inter([integer, neg(float)])])
```

After some indirection, we end up at a predicate called `normalize`,
which takes a `union`/`inter`/`neg` functor and an argument unified
with the simplified DNF. Its clause for `union` looks like so:

```prolog
normalize(union(Types), DNF) :- !,
    maplist(normalize, Types, DNFs),
    flatten_unions(DNFs, FlattenedInters),
    simplify(union(FlattenedInters), DNF).
```

That bang at the front is a
[`cut`](https://homepage.divms.uiowa.edu/~hzhang/c188/notes/ch08b-cut.pdf),
which means something like "commit".  It prevents the runtime from
[backtracking](https://en.wikipedia.org/wiki/Backtracking) through the
point at which the cut appears.  Here, it's used to ensure more
general clauses for `normalize` (which appear after --- ordering
matters) will never match a `union` even if there's some
goal/unification failure downstream.  We're never cutting for
efficiency, only for semantics.  For the concrete types in the union
--- `number`, `string` --- the recursive call, via `maplist`, will
trigger one such clause:

```prolog
normalize(Type, union([inter([Type])])) :-
    concrete(Type),
    !.
```

This is converting a concrete type into the DNF for same,
`union([inter([Type])])`, if the type is concrete.  Note that here the
cut appeares _after_ the call to `concrete` --- because we've
multiple clauses as general as `Type`, and so can't _commit_ here until we
know  `concrete` has been satisfied.  Then, we get to the
intersection:

#### The Nested Intersection

```prolog
normalize(inter(Types), DNF) :- !,
    maplist(normalize, Types, DNFs),
    distribute(DNFs, DistributedDNF),
    simplify(DistributedDNF, DNF).
```

It has `integer` and `neg(float)` to deal with, in _its_ recursive
calls.  The negation path for concrete types just puts the functor
`neg(float)` into the literal slot in the DNF, like the `normalize(Type, ..)` clause above.  It otherwise swaps
`any`/`nil` and applies [De Morgan's
laws](https://en.wikipedia.org/wiki/De_Morgan%27s_laws) to
`union`/`inter`.  `DNFs` will be a list of two top-level DNF forms:

```prolog
[union([inter([integer])]), union([inter([neg(float)])])]
```

Next, we _distribute conjunction over disjunction_, turning our
top-level DNF representations into a single DNF form.

```prolog
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
```

There are some trivial optimizations we could perform --- this
implementation overall is indended to be expressive, compact and
readable.  At this point in the program, we have this representation
for what was our nested intersection:

```prolog
union([inter([neg(float), integer])])
```

`simplify` will take us to the below, via a `maplist(simplify_inter,
...)` in the simplification logic for `union`:

```prolog
simplify_inter(inter(Literals), Inter) :-
    ( list_to_ord_set(Literals, Lits),
      ( contradictory(Lits)      -> Inter = nil
      ; disjoint_concretes(Lits) -> Inter = nil
      ; simplify_lits(Lits, Inter))).

simplify_lits(LitsIn, Inter) :-
    join_negs(LitsIn, Intermediate),
    subsume_lits(Intermediate, Minimal),
    Inter = inter(Minimal).
```

Our intersection isn't `contradictory` (it doesn't contain its own
negation or the negation of a supertype), it doesn't contain disjoint
concrete types, as negated types are not concrete,  What about `join_negs`?

```prolog
join_negs(Lits, LitsOut) :-
    findall(neg(TB),
            (member(neg(TB), Lits),
             concrete(TB),
             member(TA, Lits),
             concrete(TA),
             are_disjoint(TA, TB)),
            RedundantNegs),
    ord_subtract(Lits, RedundantNegs, LitsOut).
```

I think they've got us here.  We're checking for types which are
disjoint within an intersection, across negations, and removing the
negation --- because type `TA` (above, `integer`) cannot possibly be
augmented by `TB` (`float`, the complement of our `neg(float)`) ---
recall that `integer` and `float` are disjoint; it follows that for
every `integer`, `neg(float)` is implied.  So `LitsOut` will be the
DNF for `integer` and `subsume_lits`, whatever that is, presumably
won't do anything, with a single type.  Let's jump to the `union`
simplification logic which was invoking us, via:

```prolog
normalize(union(Types), DNF) :- !,
    maplist(normalize, Types, DNFs),
    flatten_unions(DNFs, FlattenedInters),
    simplify(union(FlattenedInters), DNF).
```

#### Union Simplification

```prolog
simplify(union(Inters), SimplifiedDNF) :-
    maplist(simplify_inter, Inters, SimplifiedInters),
    include(\=(nil), SimplifiedInters, NonNilInters),
    list_to_ord_set(NonNilInters, UniqueInters),
    ( has_complementary_inter(UniqueInters) ->
      SimplifiedDNF = union([inter([])])
    ;
    absorb(UniqueInters, MinimalInters),
    canonicalize(union(MinimalInters), SimplifiedDNF)).
````

At this point, we've flattened evrything, and processed our nested
intersection.  Our DNF looks like:

```prolog
union([inter([integer]), inter([number]), inter([string])])
```
Recall we started with
```prolog
union([number, string, inter([integer, neg(float)])])
```

`has_complementary_inter` just looks for an intersection containing a
single type and another intersection containing its negation, and
simplifies to the DNF for `any`.  We get to `absorb`:

```prolog
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
```

We remove all of the subtypes in the intersection,
`number` wins out over `integer`, and we're left with `number` and
`string`.  `canonicalize` converts the empty union to
the atom `nil`, for programmer convenience, and does little else, so our final DNF is:

```prolog
union([inter([number]), inter([string])]) % union([number, string])
```

I left out utility functions and so on, and some minor functionality,
but that's about the long and short of it.  The full source [is here](https://github.com/moea/playground/tree/main/refinement)


<a id="refinement"></a>
## Type Refinement

```prolog
:- module(refinement, [...]).

:- use_module(dnf, [...]).


predicate_type(number_p, number).
predicate_type(integer_p, integer).
...
```

For each basic type, there is a corresponding symbolic predicate,
which, when applied, has the effect of refining the type of the tested
variable depending on whether we're in true/false branch.  We're
operating statically, solely in the type domain --- we don't evaluate
anything.  `integer_p` is just an atom used in functors we can anayze,
not a Prolog predicate.

One of the things we're going to have to do when refining types in
expressions which contain `and`/`or` is perform set operations over
two type environments --- unions or intersections across all of their
types.  Let's look at that logic first.

```prolog
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
```

Where `Operator` is one of `dnf:make_union` or `dnf:make_inter`, each
of which is identical to the corresponding
`construct(union(...))`/`(construct(inter(...))` clause.  **If this is
confusing**, maybe you skipped [DNF
Construction](#construction). `get_type` defaults to `any`.
`put_dict`, at this arity, takes a key, an input dict, a value, and an
output dict.  Note going forward: dictionaries can have multiple
associations per key.  Now, our main predicate, `refine` --- we're
going to have to cover the predicate refinement case, before the
logical operators.

```prolog
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

    put_dict(Var, InitialEnv, TrueDNF, TrueEnv),
    put_dict(Var, InitialEnv, FalseDNF, FalseEnv).
```

`=..` (or `univ`) destructures a functor, for the purpose of dynamic
pattern matching, here, in the bit before the cut.  We're looking for
something shaped like `integer_p(x)`. `InitialEnv` will look like `[x:
union([integer, string])]`, but with the types
converted to DNF.

This is where our choice to use a formulaic representation pays off.
To get the type of the test variable in the case where the predicate
is true, we perform an `AND` on the types of the variable and the the
one associated with the predicate, its _refinement_ --- which is to
say, we intersect them.  To get the type of the variable in the false
case, we first negate the predicate's associated type --- or
complement its set --- and then `AND` that type with the variable's.
Let's look at the other cases.  You'll notice they're all recursive,
allowing us to arbitrarily nest boolean operators.

```prolog
refine(not(SubExpr), InitialEnv, TrueEnv, FalseEnv) :- !,
    refine(SubExpr, InitialEnv, FalseEnv, TrueEnv),
```

We just flip the argument order in our call to `refine`.  Now, for the
jucier ones:

```prolog
refine(and(ExprA, ExprB), InitialEnv, TrueEnv, FalseEnv) :- !,
    refine(ExprA, InitialEnv, EnvA_True, EnvA_False),
    refine(ExprB, EnvA_True,  TrueEnv,   EnvB_False),
    merge(dnf:make_union, EnvA_False, EnvB_False, FalseEnv).
```

This is pretty intuitive, if you look at the variable placements.  We
need to refine both subexpressions, and `EnvA_True` is the `Env` input
to the second `refine`, the `true` output of which we unify with the final
`TrueEnv`.  We calculate `FalseEnv` with an `OR` across the the types
in the `false` environments for both subexpressions, as either of them
could be false.  Finally:

```prolog
refine(or(ExprA, ExprB), InitialEnv, TrueEnv, FalseEnv) :- !,
    refine(ExprA, InitialEnv, EnvA_True, EnvA_False),
    refine(ExprB, InitialEnv, EnvB_True, EnvB_False),
    merge(dnf:make_union, EnvA_True, EnvB_True, TrueEnv),
    merge(dnf:make_inter, EnvA_False, EnvB_False, FalseEnv).
```

In contrast to `and`, there's nothing shared between the recursive
`refine` calls, because we've no information about whether the first
test succeeded.  `TrueEnv` is the pairwise `union` of the types in the
`true` environments --- we know one of them is true, and `FalseEnv` is
the result of intersecting the `false` environments --- we know both
of them are false.  Here are some examples from the tests:


```prolog
test(union_predicate_no_intersect) :-
    test_refinement(
        integer_p(x), % test
        [x: union([float, string])], % env
        [x: nil], % true
        [x: union([float, string])]). % false

test(union_negation) :-
    test_refinement(
        not(integer_p(x)),
        [x: union([integer, string])],
        [x: string],
        [x: integer]
                   ).

test(union_and) :-
    test_refinement(
        and(number_p(x), not(integer_p(x))),
        [x: union([number, string])],
        [x: inter([number, neg(integer)])],
        [x: union([integer, string])]).
```

## Conclusions

DNF turned out to be a very practical choice for this type system.
That said, it's not at all clear to me how you would represent arrow
types with it, as they cannot be decomposed into atoms.  I think a different
representation would be required.  I will explore this further.

Prolog was great fun!  I will definitely continue to use it in the future.  [Full source here](https://github.com/moea/playground/tree/main/refinement).

[^1]: ON [UPPERCASE STRINGS](https://www.typescriptlang.org/docs/handbook/2/template-literal-types.html#uppercasestringtype) WITH AN APPLICATION TO THE [ENTSCHEIDUNGSPROBLEM](https://github.com/Microsoft/TypeScript/issues/14833).
[^2]: Note that type refinement in this flow-dependent sense is not to be confused with [refinment types](https://en.wikipedia.org/wiki/Refinement_type), though they're related, and we'll implement a version of refinement types at the end of this article.
[^3]: RIP.
[^4]: Rest in Peace.
[^5]: This is a term of endearment, coming from a Lisp nerd.
[^6]: [CDuce](https://www.cduce.org/).
[^7]: Lambdas with head-destructuring would greatly enhance the experience.  Or any binding form with destructuring as powerful as rule heads.
