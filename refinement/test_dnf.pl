:- module(test_dnf, []).

:- use_module(library(plunit)).
:- use_module(dnf).

:- begin_tests(dnf_subtyping).

test('nil is subtype of nil') :-
    construct(nil, DNFNil),
    dnf_subtype_of(DNFNil, DNFNil).

test('nil is subtype of integer') :-
    construct(nil, DNFNil),
    construct(integer, DNFInt),
    dnf_subtype_of(DNFNil, DNFInt).

test('integer is not subtype of nil') :-
    construct(integer, DNFInt),
    construct(nil, DNFNil),
    \+ dnf_subtype_of(DNFInt, DNFNil).

test('integer is subtype of integer') :-
    construct(integer, DNFInt),
    dnf_subtype_of(DNFInt, DNFInt).

test('integer is subtype of number') :-
    construct(integer, DNFInt),
    construct(number, DNFNum),
    dnf_subtype_of(DNFInt, DNFNum).

test('number is not subtype of integer') :-
    construct(integer, DNFInt),
    construct(number, DNFNum),
    \+ dnf_subtype_of(DNFNum, DNFInt).

test('integer is subtype of union(number, string)') :-
    construct(integer, DNFInt),
    construct(union([number, string]), DNFNumStr),
    dnf_subtype_of(DNFInt, DNFNumStr).

test('union(integer, float) is subtype of number') :-
    construct(union([integer, float]), DNFIntFloat),
    construct(number, DNFNum),
    dnf_subtype_of(DNFIntFloat, DNFNum).

test('union(integer, string) is not subtype of number') :-
    construct(union([integer, string]), DNFIntStr),
    construct(number, DNFNum),
    \+ dnf_subtype_of(DNFIntStr, DNFNum).

test('union(integer, string) is subtype of union(number, string)') :-
    construct(union([integer, string]), DNFIntStr),
    construct(union([number, string]), DNFNumStr),
    dnf_subtype_of(DNFIntStr, DNFNumStr).

test('union(number, string) is not subtype of union(integer, string)') :-
    construct(union([integer, string]), DNFIntStr),
    construct(union([number, string]), DNFNumStr),
    \+ dnf_subtype_of(DNFNumStr, DNFIntStr).

test('inter(num, neg(str)) subtype of num') :-
    construct(inter([number, neg(string)]), DNFInter),
    construct(number, DNFNum),
    dnf_subtype_of(DNFInter, DNFNum).

test('inter(num, neg(str)) subtype of inter(num, neg(str))') :-
    construct(inter([number, neg(string)]), DNFInter),
    dnf_subtype_of(DNFInter, DNFInter).

test('inter(num, neg(str)) subtype of inter(num)') :-
    construct(inter([number, neg(string)]), DNFInterA),
    construct(inter([number]), DNFInterB),
    dnf_subtype_of(DNFInterA, DNFInterB).

test('union(inter(int, list), inter(str)) subtype of union(inter(num, list), inter(str))') :-
    construct(union([inter([integer, list]), inter([string])]), DNFA),
    construct(union([inter([number, list]), inter([string])]), DNFB),
    dnf_subtype_of(DNFA, DNFB).

test('subtype of any') :-
    construct(integer, DNFInt),
    construct(any, DNFAny),
    dnf_subtype_of(DNFInt, DNFAny).

test('any is subtype of any') :-
    construct(any, DNFAny),
    dnf_subtype_of(DNFAny, DNFAny).

test('any is not subtype of integer') :-
    construct(any, DNFAny),
    construct(integer, DNFInt),
    \+ dnf_subtype_of(DNFAny, DNFInt).

test('neg(number) subtype of neg(integer)') :-
    construct(neg(number), DNFNegNum),
    construct(neg(integer), DNFNegInt),
    dnf_subtype_of(DNFNegNum, DNFNegInt).

test('neg(integer) not subtype of neg(number)') :-
    construct(neg(number), DNFNegNum),
    construct(neg(integer), DNFNegInt),
    \+ dnf_subtype_of(DNFNegInt, DNFNegNum).

:- end_tests(dnf_subtyping).
