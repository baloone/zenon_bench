% Copyright 2012-2015 Consortium of the BWare ANR Project (ANR-12-INSE-0010)
%	  	    <http://bware.lri.fr/>
% Copyright 2012-2015 Cedric (CPR Team)
%	  	    David DELAHAYE
%	  	    <david.delahaye@cnam.fr>
% Copyright 2012-2015 LRI (VALS team)
%	  	    Sylvain CONCHON
%	  	    <sylvain.conchon@lri.fr>
% Copyright 2012-2015 Inria (Gallium, Deducteam)
%	  	    Damien DOLIGEZ
%	  	    <damien.doligez@inria.fr>
% Copyright 2012-2015 Mitsubishi Electric R&D Centre Europe
%	  	    David MENTRE
%	  	    <d.mentre@fr.merce.mee.com>
% Copyright 2012-2015 ClearSy
%	  	    Thierry LECOMTE
%	  	    <thierry.lecomte@clearsy.com>
% Copyright 2012-2015 OCamlPro
%	  	    Fabrice LE FESSANT
%		    <fabrice.le_fessant@ocamlpro.com>
%
% This file is a free software.
%
% This software is governed by the CeCILL-B license under French law and 
% abiding by the rules of distribution of free software.  
% You can use, modify and/or redistribute the software under the terms of the 
% CeCILL-B license as circulated by CEA, CNRS and INRIA at the following URL 
% "http://www.cecill.info". 
%
% As a counterpart to the access to the source code and rights to copy,
% modify and redistribute granted by the license, users are provided only
% with a limited warranty and the software's author, the holder of the
% economic rights, and the successive licensors have only limited liability. 
%
% In this respect, the user's attention is drawn to the risks associated
% with loading, using, modifying and/or developing or reproducing the
% software by the user in light of its specific status of free software,
% that may mean that it is complicated to manipulate, and that also
% therefore means that it is reserved for developers and experienced
% professionals having in-depth computer knowledge. Users are therefore
% encouraged to load and test the software's suitability as regards their
% requirements in conditions enabling the security of their systems and/or 
% data to be ensured and, more generally, to use and operate it in the 
% same conditions as regards security. 
%
% The fact that you are presently reading this means that you have had
% knowledge of the CeCILL-B license and that you accept its terms.
%
% ------------------------------------------------------------------------------

tff(bool, type, bool: $tType).

tff(true, type, true: bool).

tff(false, type, false: bool).

tff(match_bool, type, match_bool: !>[A : $tType]: ((bool * A * A) > A)).

tff(match_bool_True, axiom, ![A : $tType]: ![Z:A, Z1:A]: (match_bool(A, true,
  Z, Z1) = Z)).

tff(match_bool_False, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_bool(A, false, Z, Z1) = Z1)).

tff(true_False, axiom, ~ (true = false)).

tff(bool_inversion, axiom, ![U:bool]: ((U = true) | (U = false))).

tff(andb, type, andb: (bool * bool) > bool).

tff(andb_def, axiom, ![Y:bool]: ((andb(true, Y) = Y) & (andb(false,
  Y) = false))).

tff(orb, type, orb: (bool * bool) > bool).

tff(orb_def, axiom, ![Y:bool]: ((orb(true, Y) = true) & (orb(false,
  Y) = Y))).

tff(xorb, type, xorb: (bool * bool) > bool).

tff(xorb_def, axiom, (((xorb(true, true) = false) & (xorb(false,
  true) = true)) & ((xorb(true, false) = true) & (xorb(false,
  false) = false)))).

tff(notb, type, notb: bool > bool).

tff(notb_def, axiom, ((notb(true) = false) & (notb(false) = true))).

tff(implb, type, implb: (bool * bool) > bool).

tff(implb_def, axiom, ![X:bool]: ((implb(X, true) = true) & ((implb(true,
  false) = false) & (implb(false, false) = true)))).

tff(compatOrderMult, axiom, ![X:$int, Y:$int, Z:$int]: ($lesseq(X,Y)
  => ($lesseq(0,Z) => $lesseq($product(X,Z),$product(Y,Z))))).

tff(abs, type, abs: $int > $int).

tff(abs_def, axiom, ![X:$int]: (($lesseq(0,X) => (abs(X) = X)) & (~
  $lesseq(0,X) => (abs(X) = $uminus(X))))).

tff(abs_le, axiom, ![X:$int, Y:$int]: ($lesseq(abs(X),Y)
  <=> ($lesseq($uminus(Y),X) & $lesseq(X,Y)))).

tff(abs_pos, axiom, ![X:$int]: $lesseq(0,abs(X))).

tff(div, type, div: ($int * $int) > $int).

tff(mod, type, mod: ($int * $int) > $int).

tff(div_mod, axiom, ![X:$int, Y:$int]: (~ (Y = 0)
  => (X = $sum($product(Y,div(X, Y)),mod(X, Y))))).

tff(div_bound, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(0,Y))
  => ($lesseq(0,div(X, Y)) & $lesseq(div(X, Y),X)))).

tff(mod_bound, axiom, ![X:$int, Y:$int]: (~ (Y = 0)
  => ($less($uminus(abs(Y)),mod(X, Y)) & $less(mod(X, Y),abs(Y))))).

tff(div_sign_pos, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(0,Y))
  => $lesseq(0,div(X, Y)))).

tff(div_sign_neg, axiom, ![X:$int, Y:$int]: (($lesseq(X,0) & $less(0,Y))
  => $lesseq(div(X, Y),0))).

tff(mod_sign_pos, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & ~ (Y = 0))
  => $lesseq(0,mod(X, Y)))).

tff(mod_sign_neg, axiom, ![X:$int, Y:$int]: (($lesseq(X,0) & ~ (Y = 0))
  => $lesseq(mod(X, Y),0))).

tff(rounds_toward_zero, axiom, ![X:$int, Y:$int]: (~ (Y = 0)
  => $lesseq(abs($product(div(X, Y),Y)),abs(X)))).

tff(div_1, axiom, ![X:$int]: (div(X, 1) = X)).

tff(mod_1, axiom, ![X:$int]: (mod(X, 1) = 0)).

tff(div_inf, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(X,Y))
  => (div(X, Y) = 0))).

tff(mod_inf, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(X,Y))
  => (mod(X, Y) = X))).

tff(div_mult, axiom, ![X:$int, Y:$int, Z:$int]: (($less(0,X) & ($lesseq(0,Y)
  & $lesseq(0,Z))) => (div($sum($product(X,Y),Z), X) = $sum(Y,div(Z, X))))).

tff(mod_mult, axiom, ![X:$int, Y:$int, Z:$int]: (($less(0,X) & ($lesseq(0,Y)
  & $lesseq(0,Z))) => (mod($sum($product(X,Y),Z), X) = mod(Z, X)))).

tff(set, type, set: $tType > $tType).

tff(mem, type, mem: !>[A : $tType]: ((A * set(A)) > $o)).

tff(infix_eqeq, type, infix_eqeq: !>[A : $tType]: ((set(A) * set(A)) > $o)).

tff(infix_eqeq_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (infix_eqeq(A, S, T) <=> ![X:A]: (mem(A, X, S) <=> mem(A, X, T)))).

tff(power, type, power: !>[A : $tType]: (set(A) > set(set(A)))).

tff(non_empty_power, type, non_empty_power: !>[A : $tType]: (set(A) >
  set(set(A)))).

tff(subset, type, subset: !>[A : $tType]: ((set(A) * set(A)) > $o)).

tff(subset_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]: (subset(A, S, T)
  <=> mem(set(A), S, power(A, T)))).

tff(subsetnoteq, type, subsetnoteq: !>[A : $tType]: ((set(A) * set(A)) >
  $o)).

tff(subsetnoteq_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (subsetnoteq(A, S, T) <=> (subset(A, S, T) & ~ infix_eqeq(A, S, T)))).

tff(empty, type, empty: !>[A : $tType]: set(A)).

tff(is_empty, type, is_empty: !>[A : $tType]: (set(A) > $o)).

tff(is_empty_def, axiom, ![A : $tType]: ![S:set(A)]: (is_empty(A, S) <=> ![X:
  A]: ~ mem(A, X, S))).

tff(empty_def1, axiom, ![A : $tType]: is_empty(A, empty(A))).

tff(empty1, axiom, ![A : $tType]: ![X:A]: ~ mem(A, X, empty(A))).

tff(add, type, add: !>[A : $tType]: ((A * set(A)) > set(A))).

tff(add_def1, axiom, ![A : $tType]: ![X:A, Y:A]: ![S:set(A)]: (mem(A, X,
  add(A, Y, S)) <=> ((X = Y) | mem(A, X, S)))).

tff(singleton, type, singleton: !>[A : $tType]: (A > set(A))).

tff(mem_singleton, axiom, ![A : $tType]: ![X:A, Y:A]: (mem(A, X,
  singleton(A, Y)) <=> (X = Y))).

tff(remove, type, remove: !>[A : $tType]: ((A * set(A)) > set(A))).

tff(remove_def1, axiom, ![A : $tType]: ![X:A, Y:A, S:set(A)]: (mem(A, X,
  remove(A, Y, S)) <=> (~ (X = Y) & mem(A, X, S)))).

tff(all, type, all: !>[A : $tType]: set(A)).

tff(all_def, axiom, ![A : $tType]: ![X:A]: mem(A, X, all(A))).

tff(union, type, union: !>[A : $tType]: ((set(A) * set(A)) > set(A))).

tff(mem_union, axiom, ![A : $tType]: ![S:set(A), T:set(A), X:A]: (mem(A, X,
  union(A, S, T)) <=> (mem(A, X, S) | mem(A, X, T)))).

tff(inter, type, inter: !>[A : $tType]: ((set(A) * set(A)) > set(A))).

tff(mem_inter, axiom, ![A : $tType]: ![S:set(A), T:set(A), X:A]: (mem(A, X,
  inter(A, S, T)) <=> (mem(A, X, S) & mem(A, X, T)))).

tff(diff, type, diff: !>[A : $tType]: ((set(A) * set(A)) > set(A))).

tff(mem_diff, axiom, ![A : $tType]: ![S:set(A), T:set(A), X:A]: (mem(A, X,
  diff(A, S, T)) <=> (mem(A, X, S) & ~ mem(A, X, T)))).

tff(b_bool, type, b_bool: set(bool)).

tff(mem_b_bool, axiom, ![X:bool]: mem(bool, X, b_bool)).

tff(integer, type, integer: set($int)).

tff(mem_integer, axiom, ![X:$int]: mem($int, X, integer)).

tff(natural, type, natural: set($int)).

tff(mem_natural, axiom, ![X:$int]: (mem($int, X, natural) <=> $lesseq(0,X))).

tff(natural1, type, natural1: set($int)).

tff(mem_natural1, axiom, ![X:$int]: (mem($int, X, natural1) <=> $less(0,X))).

tff(nat, type, nat: set($int)).

tff(mem_nat, axiom, ![X:$int]: (mem($int, X, nat) <=> ($lesseq(0,X)
  & $lesseq(X,2147483647)))).

tff(nat1, type, nat1: set($int)).

tff(mem_nat1, axiom, ![X:$int]: (mem($int, X, nat1) <=> ($less(0,X)
  & $lesseq(X,2147483647)))).

tff(bounded_int, type, bounded_int: set($int)).

tff(mem_bounded_int, axiom, ![X:$int]: (mem($int, X, bounded_int)
  <=> ($lesseq($uminus(2147483647),X) & $lesseq(X,2147483647)))).

tff(mk, type, mk: ($int * $int) > set($int)).

tff(mem_interval, axiom, ![X:$int, A:$int, B:$int]: (mem($int, X, mk(A, B))
  <=> ($lesseq(A,X) & $lesseq(X,B)))).

tff(tuple2, type, tuple2: ($tType * $tType) > $tType).

tff(tuple21, type, tuple21: !>[A : $tType, A1 : $tType]: ((A1 * A) >
  tuple2(A1, A))).

tff(tuple2_proj_1, type, tuple2_proj_1: !>[A : $tType, A1 : $tType]:
  (tuple2(A1, A) > A1)).

tff(tuple2_proj_1_def, axiom, ![A : $tType, A1 : $tType]: ![U:A1, U1:A]:
  (tuple2_proj_1(A, A1, tuple21(A, A1, U, U1)) = U)).

tff(tuple2_proj_2, type, tuple2_proj_2: !>[A : $tType, A1 : $tType]:
  (tuple2(A1, A) > A)).

tff(tuple2_proj_2_def, axiom, ![A : $tType, A1 : $tType]: ![U:A1, U1:A]:
  (tuple2_proj_2(A, A1, tuple21(A, A1, U, U1)) = U1)).

tff(tuple2_inversion, axiom, ![A : $tType, A1 : $tType]: ![U:tuple2(A1, A)]:
  (U = tuple21(A, A1, tuple2_proj_1(A, A1, U), tuple2_proj_2(A, A1, U)))).

tff(times, type, times: !>[A : $tType, B : $tType]: ((set(A) * set(B)) >
  set(tuple2(A, B)))).

tff(mem_times, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:set(B), X:A,
  Y:B]: (mem(tuple2(A, B), tuple21(B, A, X, Y), times(A, B, S, T))
  <=> (mem(A, X, S) & mem(B, Y, T)))).

tff(mem_power, axiom, ![A : $tType]: ![S:set(A), T:set(A)]: (mem(set(A), S,
  power(A, T)) <=> ![X:A]: (mem(A, X, S) => mem(A, X, T)))).

tff(mem_non_empty_power, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (mem(set(A), S, non_empty_power(A, T)) <=> (![X:A]: (mem(A, X, S)
  => mem(A, X, T)) & ~ infix_eqeq(A, S, empty(A))))).

tff(choose, type, choose: !>[A : $tType]: (set(A) > A)).

tff(relation, type, relation: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_relation, axiom, ![A : $tType, B : $tType]: ![U:set(A), V:set(B), R:
  set(tuple2(A, B))]: (mem(set(tuple2(A, B)), R, relation(A, B, U, V))
  <=> ![X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X, Y), R) => (mem(A, X,
  U) & mem(B, Y, V))))).

tff(inverse, type, inverse: !>[A : $tType, B : $tType]: (set(tuple2(A, B)) >
  set(tuple2(B, A)))).

tff(mem_inverse, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), X:
  B, Y:A]: (mem(tuple2(B, A), tuple21(A, B, X, Y), inverse(A, B, P))
  <=> mem(tuple2(A, B), tuple21(B, A, Y, X), P))).

tff(dom, type, dom: !>[A : $tType, B : $tType]: (set(tuple2(A, B)) >
  set(A))).

tff(mem_dom, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), X:A]:
  (mem(A, X, dom(A, B, P)) <=> ?[B1:B]: mem(tuple2(A, B), tuple21(B, A, X,
  B1), P))).

tff(ran, type, ran: !>[A : $tType, B : $tType]: (set(tuple2(A, B)) >
  set(B))).

tff(mem_ran, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), X:B]:
  (mem(B, X, ran(A, B, P)) <=> ?[A1:A]: mem(tuple2(A, B), tuple21(B, A, A1,
  X), P))).

tff(semicolon, type, semicolon: !>[A : $tType, B : $tType, C : $tType]:
  ((set(tuple2(A, B)) * set(tuple2(B, C))) > set(tuple2(A, C)))).

tff(mem_semicolon, axiom, ![A : $tType, B : $tType, C : $tType]: ![P:
  set(tuple2(A, B)), Q:set(tuple2(B, C)), X:A, Y:C]:
  (mem(tuple2(A, C), tuple21(C, A, X, Y), semicolon(A, B, C, P, Q)) <=> ?[B1:
  B]: (mem(tuple2(A, B), tuple21(B, A, X, B1), P)
  & mem(tuple2(B, C), tuple21(C, B, B1, Y), Q)))).

tff(semicolon_back, type, semicolon_back: !>[A : $tType, B : $tType,
  C : $tType]: ((set(tuple2(B, C)) * set(tuple2(A, B))) >
  set(tuple2(A, C)))).

tff(semicolon_back1, axiom, ![A : $tType, B : $tType, C : $tType]: ![P:
  set(tuple2(A, B)), Q:set(tuple2(B, C))]: (semicolon_back(A, B, C, Q,
  P) = semicolon(A, B, C, P, Q))).

tff(id, type, id: !>[A : $tType]: (set(A) > set(tuple2(A, A)))).

tff(mem_id, axiom, ![A : $tType]: ![U:set(A), X:A, Y:A]:
  (mem(tuple2(A, A), tuple21(A, A, X, Y), id(A, U)) <=> (mem(A, X, U)
  & (X = Y)))).

tff(domain_restriction, type, domain_restriction: !>[A : $tType, B : $tType]:
  ((set(A) * set(tuple2(A, B))) > set(tuple2(A, B)))).

tff(mem_domain_restriction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), S:set(A), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), domain_restriction(A, B, S, P)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), P) & mem(A, X, S)))).

tff(range_restriction, type, range_restriction: !>[A : $tType, B : $tType]:
  ((set(tuple2(A, B)) * set(B)) > set(tuple2(A, B)))).

tff(mem_range_restriction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), T:set(B), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), range_restriction(A, B, P, T)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), P) & mem(B, Y, T)))).

tff(domain_substraction, type, domain_substraction: !>[A : $tType,
  B : $tType]: ((set(A) * set(tuple2(A, B))) > set(tuple2(A, B)))).

tff(mem_domain_substraction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), S:set(A), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), domain_substraction(A, B, S, P)) <=> (mem(tuple2(A, B), tuple21(B,
  A, X, Y), P) & ~ mem(A, X, S)))).

tff(range_substraction, type, range_substraction: !>[A : $tType, B : $tType]:
  ((set(tuple2(A, B)) * set(B)) > set(tuple2(A, B)))).

tff(mem_range_substraction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), T:set(B), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), range_substraction(A, B, P, T)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), P) & ~ mem(B, Y, T)))).

tff(image, type, image: !>[A : $tType, B : $tType]: ((set(tuple2(A, B)) *
  set(A)) > set(B))).

tff(mem_image, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), W:
  set(A), X:B]: (mem(B, X, image(A, B, P, W)) <=> ?[A1:A]: (mem(A, A1, W)
  & mem(tuple2(A, B), tuple21(B, A, A1, X), P)))).

tff(infix_lspl, type, infix_lspl: !>[A : $tType, B : $tType]:
  ((set(tuple2(A, B)) * set(tuple2(A, B))) > set(tuple2(A, B)))).

tff(mem_overriding, axiom, ![A : $tType, B : $tType]: ![Q:set(tuple2(A, B)),
  P:set(tuple2(A, B)), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X, Y),
  infix_lspl(A, B, Q, P)) <=> ((mem(tuple2(A, B), tuple21(B, A, X, Y), Q) & ~
  mem(A, X, dom(A, B, P))) | mem(tuple2(A, B), tuple21(B, A, X, Y), P)))).

tff(direct_product, type, direct_product: !>[A : $tType, B : $tType,
  C : $tType]: ((set(tuple2(A, B)) * set(tuple2(A, C))) >
  set(tuple2(A, tuple2(B, C))))).

tff(mem_direct_product, axiom, ![A : $tType, B : $tType, C : $tType]: ![F:
  set(tuple2(A, B)), G:set(tuple2(A, C)), X:A, Y:B, Z:C]:
  (mem(tuple2(A, tuple2(B, C)), tuple21(tuple2(B, C), A, X, tuple21(C, B, Y,
  Z)), direct_product(A, B, C, F, G)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), F) & mem(tuple2(A, C), tuple21(C, A, X, Z), G)))).

tff(prj1, type, prj1: !>[A : $tType, B : $tType]: (tuple2(set(A), set(B)) >
  set(tuple2(tuple2(A, B), A)))).

tff(mem_proj_op_1, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:set(B), X:
  A, Y:B, Z:A]: (mem(tuple2(tuple2(A, B), A), tuple21(A,
  tuple2(A, B), tuple21(B, A, X, Y), Z), prj1(A, B, tuple21(set(B),
  set(A), S, T))) <=> (mem(tuple2(tuple2(A, B), A), tuple21(A,
  tuple2(A, B), tuple21(B, A, X, Y), Z), times(tuple2(A, B), A, times(A,
  B, S, T), S)) & (Z = X)))).

tff(prj2, type, prj2: !>[A : $tType, B : $tType]: (tuple2(set(A), set(B)) >
  set(tuple2(tuple2(A, B), B)))).

tff(mem_proj_op_2, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:set(B), X:
  A, Y:B, Z:B]: (mem(tuple2(tuple2(A, B), B), tuple21(B,
  tuple2(A, B), tuple21(B, A, X, Y), Z), prj2(A, B, tuple21(set(B),
  set(A), S, T))) <=> (mem(tuple2(tuple2(A, B), B), tuple21(B,
  tuple2(A, B), tuple21(B, A, X, Y), Z), times(tuple2(A, B), B, times(A,
  B, S, T), T)) & (Z = Y)))).

tff(parallel_product, type, parallel_product: !>[A : $tType, B : $tType,
  C : $tType, D : $tType]: ((set(tuple2(A, B)) * set(tuple2(C, D))) >
  set(tuple2(tuple2(A, C), tuple2(B, D))))).

tff(mem_parallel_product, axiom, ![A : $tType, B : $tType, C : $tType,
  D : $tType]: ![H:set(tuple2(A, B)), K:set(tuple2(C, D)), X:A, Y:C, Z:B, W:
  D]: (mem(tuple2(tuple2(A, C), tuple2(B, D)), tuple21(tuple2(B, D),
  tuple2(A, C), tuple21(C, A, X, Y), tuple21(D, B, Z, W)),
  parallel_product(A, B, C, D, H, K)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Z), H) & mem(tuple2(C, D), tuple21(D, C, Y, W), K)))).

tff(infix_plmngt, type, infix_plmngt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_function_set, axiom, ![A : $tType, B : $tType]: ![S:set(A),
  T:set(B), F:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), F, infix_plmngt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), F, relation(A, B, S, T)) & ![X:A, Y1:
  B, Y2:B]: ((mem(tuple2(A, B), tuple21(B, A, X, Y1), F)
  & mem(tuple2(A, B), tuple21(B, A, X, Y2), F)) => (Y1 = Y2))))).

tff(infix_mnmngt, type, infix_mnmngt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_function_set, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:
  set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X, infix_mnmngt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_plmngt(A, B, S, T))
  & infix_eqeq(A, dom(A, B, X), S)))).

tff(infix_gtplgt, type, infix_gtplgt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_injection_set, axiom, ![A : $tType, B : $tType]: ![S:
  set(A), T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_gtplgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_plmngt(A,
  B, S, T)) & mem(set(tuple2(B, A)), inverse(A, B, X), infix_plmngt(B, A, T,
  S))))).

tff(infix_gtmngt, type, infix_gtmngt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_injection_set, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:
  set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X, infix_gtmngt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_gtplgt(A, B, S, T))
  & mem(set(tuple2(A, B)), X, infix_mnmngt(A, B, S, T))))).

tff(infix_plmngtgt, type, infix_plmngtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_surjection_set, axiom, ![A : $tType, B : $tType]: ![S:
  set(A), T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_plmngtgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_plmngt(A,
  B, S, T)) & infix_eqeq(B, ran(A, B, X), T)))).

tff(infix_mnmngtgt, type, infix_mnmngtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_surjection_set, axiom, ![A : $tType, B : $tType]: ![S:set(A),
  T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_mnmngtgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X,
  infix_plmngtgt(A, B, S, T)) & mem(set(tuple2(A, B)), X, infix_mnmngt(A,
  B, S, T))))).

tff(infix_gtplgtgt, type, infix_gtplgtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_bijection_set, axiom, ![A : $tType, B : $tType]: ![S:
  set(A), T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_gtplgtgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_gtplgt(A,
  B, S, T)) & mem(set(tuple2(A, B)), X, infix_plmngtgt(A, B, S, T))))).

tff(infix_gtmngtgt, type, infix_gtmngtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_bijection_set, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:
  set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X, infix_gtmngtgt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_gtmngt(A, B, S, T))
  & mem(set(tuple2(A, B)), X, infix_mnmngtgt(A, B, S, T))))).

tff(apply, type, apply: !>[A : $tType, B : $tType]: ((set(tuple2(A, B)) *
  A) > B)).

tff(apply_def0, axiom, ![A : $tType, B : $tType]: ![F:set(tuple2(A, B)), S:
  set(A), T:set(B), A1:A]: ((mem(set(tuple2(A, B)), F, infix_plmngt(A, B, S,
  T)) & mem(A, A1, dom(A, B, F))) => mem(tuple2(A, B), tuple21(B, A, A1,
  apply(A, B, F, A1)), F))).

tff(apply_def2, axiom, ![A : $tType, B : $tType]: ![F:set(tuple2(A, B)), S:
  set(A), T:set(B), A1:A, B1:B]: ((mem(set(tuple2(A, B)), F, infix_plmngt(A,
  B, S, T)) & mem(tuple2(A, B), tuple21(B, A, A1, B1), F)) => (apply(A, B, F,
  A1) = B1))).

tff(seq_length, type, seq_length: !>[A : $tType]: (($int * set(A)) >
  set(set(tuple2($int, A))))).

tff(seq_length_def, axiom, ![A : $tType]: ![N:$int, S:set(A)]:
  (seq_length(A, N, S) = infix_mnmngt($int, A, mk(1, N), S))).

tff(size, type, size: !>[A : $tType]: (set(tuple2($int, A)) > $int)).

tff(size_def, axiom, ![A : $tType]: ![N:$int, S:set(A), R:
  set(tuple2($int, A))]: (($lesseq(0,N) & mem(set(tuple2($int, A)), R,
  seq_length(A, N, S))) => (size(A, R) = N))).

tff(seq, type, seq: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(seq_def, axiom, ![A : $tType]: ![S:set(A), R:set(tuple2($int, A))]:
  (mem(set(tuple2($int, A)), R, seq(A, S)) <=> ($lesseq(0,size(A, R))
  & mem(set(tuple2($int, A)), R, seq_length(A, size(A, R), S))))).

tff(seq1, type, seq1: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(iseq, type, iseq: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(iseq1, type, iseq1: !>[A : $tType]: (set(A) >
  set(set(tuple2($int, A))))).

tff(perm, type, perm: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(insert_in_front, type, insert_in_front: !>[A : $tType]: ((A *
  set(tuple2($int, A))) > set(tuple2($int, A)))).

tff(insert_at_tail, type, insert_at_tail: !>[A : $tType]:
  ((set(tuple2($int, A)) * A) > set(tuple2($int, A)))).

tff(tail, type, tail: !>[A : $tType]: (set(tuple2($int, A)) >
  set(tuple2($int, A)))).

tff(last, type, last: !>[A : $tType]: (set(tuple2($int, A)) > A)).

tff(first, type, first: !>[A : $tType]: (set(tuple2($int, A)) > A)).

tff(front, type, front: !>[A : $tType]: (set(tuple2($int, A)) >
  set(tuple2($int, A)))).

tff(concatenation, type, concatenation: !>[A : $tType]:
  ((set(tuple2($int, A)) * set(tuple2($int, A))) > set(tuple2($int, A)))).

tff(conc, type, conc: !>[A : $tType]:
  (set(tuple2($int, set(tuple2($int, A)))) > set(tuple2($int, A)))).

tff(is_finite_subset, type, is_finite_subset: !>[A : $tType]: ((set(A) *
  set(A) * $int) > $o)).

tff(empty2, axiom, ![A : $tType]: ![S:set(A)]: is_finite_subset(A, empty(A),
  S, 0)).

tff(add_mem, axiom, ![A : $tType]: ![X:A, S1:set(A), S2:set(A), C:$int]:
  (is_finite_subset(A, S1, S2, C) => (mem(A, X, S2) => (mem(A, X, S1)
  => is_finite_subset(A, add(A, X, S1), S2, C))))).

tff(add_notmem, axiom, ![A : $tType]: ![X:A, S1:set(A), S2:set(A), C:$int]:
  (is_finite_subset(A, S1, S2, C) => (mem(A, X, S2) => (~ mem(A, X, S1)
  => is_finite_subset(A, add(A, X, S1), S2, $sum(C,1)))))).

tff(is_finite_subset_inversion, axiom, ![A : $tType]: ![Z:set(A), Z1:
  set(A), Z2:$int]: (is_finite_subset(A, Z, Z1, Z2) => ((?[S:set(A)]:
  (((Z = empty(A)) & (Z1 = S)) & (Z2 = 0)) | ?[X:A, S1:set(A), S2:set(A), C:
  $int]: (is_finite_subset(A, S1, S2, C) & (mem(A, X, S2) & (mem(A, X, S1)
  & (((Z = add(A, X, S1)) & (Z1 = S2)) & (Z2 = C)))))) | ?[X:A, S1:set(A),
  S2:set(A), C:$int]: (is_finite_subset(A, S1, S2, C) & (mem(A, X, S2) & (~
  mem(A, X, S1) & (((Z = add(A, X, S1)) & (Z1 = S2))
  & (Z2 = $sum(C,1))))))))).

tff(finite_subsets, type, finite_subsets: !>[A : $tType]: (set(A) >
  set(set(A)))).

tff(finite_subsets_def, axiom, ![A : $tType]: ![S:set(A), X:set(A)]:
  (mem(set(A), X, finite_subsets(A, S)) <=> ?[C:$int]: is_finite_subset(A, X,
  S, C))).

tff(non_empty_finite_subsets, type, non_empty_finite_subsets: !>[A : $tType]:
  (set(A) > set(set(A)))).

tff(non_empty_finite_subsets_def, axiom, ![A : $tType]: ![S:set(A), X:
  set(A)]: (mem(set(A), X, non_empty_finite_subsets(A, S)) <=> ?[C:$int]:
  (is_finite_subset(A, X, S, C) & ~ infix_eqeq(A, X, empty(A))))).

tff(card, type, card: !>[A : $tType]: (set(A) > $int)).

tff(card_def, axiom, ![A : $tType]: ![S:set(A), X:set(A), C:$int]:
  (is_finite_subset(A, X, S, C) => (card(A, X) = C))).

tff(min, type, min: set($int) > $int).

tff(min_belongs, axiom, ![S:set($int)]: ((subset($int, S, natural) & ~
  infix_eqeq($int, S, empty($int))) => mem($int, min(S), S))).

tff(min_is_min, axiom, ![S:set($int), X:$int]: ((subset($int, S, natural)
  & mem($int, X, S)) => $lesseq(min(S),X))).

tff(max, type, max: set($int) > $int).

tff(max_belongs, axiom, ![S:set($int)]: (mem(set($int), S,
  non_empty_finite_subsets($int, natural)) => mem($int, max(S), S))).

tff(max_is_max, axiom, ![S:set($int), X:$int]: ((mem(set($int), S,
  finite_subsets($int, natural)) & mem($int, X, S)) => $lesseq(X,max(S)))).

tff(iterate, type, iterate: !>[A : $tType]:
  (tuple2(set(tuple2(A, A)), $int) > set(tuple2(A, A)))).

tff(iterate_def, axiom, ![A : $tType]: ![A1:set(tuple2(A, A)), B:$int]:
  (((B = 0) => (iterate(A, tuple21($int, set(tuple2(A, A)), A1,
  B)) = id(A, dom(A, A, A1)))) & (~ (B = 0) => (iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, B)) = semicolon(A, A, A, iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, $difference(B,1))), A1))))).

tff(closure, type, closure: !>[A : $tType]: (set(tuple2(A, A)) >
  set(tuple2(A, A)))).

tff(closure_def, axiom, ![A : $tType]: ![A1:set(tuple2(A, A)), U:
  tuple2(A, A)]: (mem(tuple2(A, A), U, closure(A, A1)) <=> ?[X:$int]:
  ($lesseq(0,X) & mem(tuple2(A, A), U, iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, X)))))).

tff(closure1, type, closure1: !>[A : $tType]: (set(tuple2(A, A)) >
  set(tuple2(A, A)))).

tff(closure1_def, axiom, ![A : $tType]: ![A1:set(tuple2(A, A)), U:
  tuple2(A, A)]: (mem(tuple2(A, A), U, closure1(A, A1)) <=> ?[X:$int]:
  ($less(0,X) & mem(tuple2(A, A), U, iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, X)))))).

tff(generalized_union, type, generalized_union: !>[A : $tType]:
  (set(set(A)) > set(A))).

tff(generalized_union_def, axiom, ![A : $tType]: ![A1:set(set(A)), X:A]:
  (mem(A, X, generalized_union(A, A1)) <=> ?[B:set(A)]: (mem(set(A), B, A1)
  & mem(A, X, B)))).

tff(uninterpreted_type, type, uninterpreted_type: $tType).

tff(enum_ETAT_AUTOMATE, type, enum_ETAT_AUTOMATE: $tType).

tff(e_Traitement_carte, type, e_Traitement_carte: enum_ETAT_AUTOMATE).

tff(e_Traitement_code, type, e_Traitement_code: enum_ETAT_AUTOMATE).

tff(e_Traitement_somme, type, e_Traitement_somme: enum_ETAT_AUTOMATE).

tff(e_Distribution_billets, type, e_Distribution_billets:
  enum_ETAT_AUTOMATE).

tff(e_Restitution_carte, type, e_Restitution_carte: enum_ETAT_AUTOMATE).

tff(e_Confiscation_carte, type, e_Confiscation_carte: enum_ETAT_AUTOMATE).

tff(e_Veille, type, e_Veille: enum_ETAT_AUTOMATE).

tff(match_enum_ETAT_AUTOMATE, type, match_enum_ETAT_AUTOMATE: !>[A : $tType]:
  ((enum_ETAT_AUTOMATE * A * A * A * A * A * A * A) > A)).

tff(match_enum_ETAT_AUTOMATE_E_Traitement_carte, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A]:
  (match_enum_ETAT_AUTOMATE(A, e_Traitement_carte, Z, Z1, Z2, Z3, Z4, Z5,
  Z6) = Z)).

tff(match_enum_ETAT_AUTOMATE_E_Traitement_code, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A]:
  (match_enum_ETAT_AUTOMATE(A, e_Traitement_code, Z, Z1, Z2, Z3, Z4, Z5,
  Z6) = Z1)).

tff(match_enum_ETAT_AUTOMATE_E_Traitement_somme, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A]:
  (match_enum_ETAT_AUTOMATE(A, e_Traitement_somme, Z, Z1, Z2, Z3, Z4, Z5,
  Z6) = Z2)).

tff(match_enum_ETAT_AUTOMATE_E_Distribution_billets, axiom, ![A : $tType]:
  ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A]:
  (match_enum_ETAT_AUTOMATE(A, e_Distribution_billets, Z, Z1, Z2, Z3, Z4, Z5,
  Z6) = Z3)).

tff(match_enum_ETAT_AUTOMATE_E_Restitution_carte, axiom, ![A : $tType]: ![Z:
  A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A]:
  (match_enum_ETAT_AUTOMATE(A, e_Restitution_carte, Z, Z1, Z2, Z3, Z4, Z5,
  Z6) = Z4)).

tff(match_enum_ETAT_AUTOMATE_E_Confiscation_carte, axiom, ![A : $tType]: ![Z:
  A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A]:
  (match_enum_ETAT_AUTOMATE(A, e_Confiscation_carte, Z, Z1, Z2, Z3, Z4, Z5,
  Z6) = Z5)).

tff(match_enum_ETAT_AUTOMATE_E_Veille, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:
  A, Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_ETAT_AUTOMATE(A, e_Veille, Z, Z1,
  Z2, Z3, Z4, Z5, Z6) = Z6)).

tff(e_Traitement_carte_E_Traitement_code, axiom, ~
  (e_Traitement_carte = e_Traitement_code)).

tff(e_Traitement_carte_E_Traitement_somme, axiom, ~
  (e_Traitement_carte = e_Traitement_somme)).

tff(e_Traitement_carte_E_Distribution_billets, axiom, ~
  (e_Traitement_carte = e_Distribution_billets)).

tff(e_Traitement_carte_E_Restitution_carte, axiom, ~
  (e_Traitement_carte = e_Restitution_carte)).

tff(e_Traitement_carte_E_Confiscation_carte, axiom, ~
  (e_Traitement_carte = e_Confiscation_carte)).

tff(e_Traitement_carte_E_Veille, axiom, ~ (e_Traitement_carte = e_Veille)).

tff(e_Traitement_code_E_Traitement_somme, axiom, ~
  (e_Traitement_code = e_Traitement_somme)).

tff(e_Traitement_code_E_Distribution_billets, axiom, ~
  (e_Traitement_code = e_Distribution_billets)).

tff(e_Traitement_code_E_Restitution_carte, axiom, ~
  (e_Traitement_code = e_Restitution_carte)).

tff(e_Traitement_code_E_Confiscation_carte, axiom, ~
  (e_Traitement_code = e_Confiscation_carte)).

tff(e_Traitement_code_E_Veille, axiom, ~ (e_Traitement_code = e_Veille)).

tff(e_Traitement_somme_E_Distribution_billets, axiom, ~
  (e_Traitement_somme = e_Distribution_billets)).

tff(e_Traitement_somme_E_Restitution_carte, axiom, ~
  (e_Traitement_somme = e_Restitution_carte)).

tff(e_Traitement_somme_E_Confiscation_carte, axiom, ~
  (e_Traitement_somme = e_Confiscation_carte)).

tff(e_Traitement_somme_E_Veille, axiom, ~ (e_Traitement_somme = e_Veille)).

tff(e_Distribution_billets_E_Restitution_carte, axiom, ~
  (e_Distribution_billets = e_Restitution_carte)).

tff(e_Distribution_billets_E_Confiscation_carte, axiom, ~
  (e_Distribution_billets = e_Confiscation_carte)).

tff(e_Distribution_billets_E_Veille, axiom, ~
  (e_Distribution_billets = e_Veille)).

tff(e_Restitution_carte_E_Confiscation_carte, axiom, ~
  (e_Restitution_carte = e_Confiscation_carte)).

tff(e_Restitution_carte_E_Veille, axiom, ~ (e_Restitution_carte = e_Veille)).

tff(e_Confiscation_carte_E_Veille, axiom, ~
  (e_Confiscation_carte = e_Veille)).

tff(enum_ETAT_AUTOMATE_inversion, axiom, ![U:enum_ETAT_AUTOMATE]:
  (((((((U = e_Traitement_carte) | (U = e_Traitement_code))
  | (U = e_Traitement_somme)) | (U = e_Distribution_billets))
  | (U = e_Restitution_carte)) | (U = e_Confiscation_carte))
  | (U = e_Veille))).

tff(set_enum_ETAT_AUTOMATE, type, set_enum_ETAT_AUTOMATE:
  set(enum_ETAT_AUTOMATE)).

tff(set_enum_ETAT_AUTOMATE_axiom, axiom, ![X:enum_ETAT_AUTOMATE]:
  mem(enum_ETAT_AUTOMATE, X, set_enum_ETAT_AUTOMATE)).

tff(enum_ETAT_DAB, type, enum_ETAT_DAB: $tType).

tff(e_Hors_service, type, e_Hors_service: enum_ETAT_DAB).

tff(e_En_service, type, e_En_service: enum_ETAT_DAB).

tff(match_enum_ETAT_DAB, type, match_enum_ETAT_DAB: !>[A : $tType]:
  ((enum_ETAT_DAB * A * A) > A)).

tff(match_enum_ETAT_DAB_E_Hors_service, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_enum_ETAT_DAB(A, e_Hors_service, Z, Z1) = Z)).

tff(match_enum_ETAT_DAB_E_En_service, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_enum_ETAT_DAB(A, e_En_service, Z, Z1) = Z1)).

tff(e_Hors_service_E_En_service, axiom, ~ (e_Hors_service = e_En_service)).

tff(enum_ETAT_DAB_inversion, axiom, ![U:enum_ETAT_DAB]: ((U = e_Hors_service)
  | (U = e_En_service))).

tff(set_enum_ETAT_DAB, type, set_enum_ETAT_DAB: set(enum_ETAT_DAB)).

tff(set_enum_ETAT_DAB_axiom, axiom, ![X:enum_ETAT_DAB]: mem(enum_ETAT_DAB, X,
  set_enum_ETAT_DAB)).

tff(enum_STATUT, type, enum_STATUT: $tType).

tff(e_Valide, type, e_Valide: enum_STATUT).

tff(e_Invalide, type, e_Invalide: enum_STATUT).

tff(e_Illisible, type, e_Illisible: enum_STATUT).

tff(e_Interdite, type, e_Interdite: enum_STATUT).

tff(e_Perimee, type, e_Perimee: enum_STATUT).

tff(e_Epuisee, type, e_Epuisee: enum_STATUT).

tff(e_Nouvel, type, e_Nouvel: enum_STATUT).

tff(e_Dernier, type, e_Dernier: enum_STATUT).

tff(e_Hors_delai, type, e_Hors_delai: enum_STATUT).

tff(e_Incident, type, e_Incident: enum_STATUT).

tff(match_enum_STATUT, type, match_enum_STATUT: !>[A : $tType]:
  ((enum_STATUT * A * A * A * A * A * A * A * A * A * A) > A)).

tff(match_enum_STATUT_E_Valide, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:
  A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]: (match_enum_STATUT(A, e_Valide, Z,
  Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9) = Z)).

tff(match_enum_STATUT_E_Invalide, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_STATUT(A, e_Invalide, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z1)).

tff(match_enum_STATUT_E_Illisible, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_STATUT(A, e_Illisible, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z2)).

tff(match_enum_STATUT_E_Interdite, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_STATUT(A, e_Interdite, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z3)).

tff(match_enum_STATUT_E_Perimee, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:
  A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]: (match_enum_STATUT(A, e_Perimee, Z,
  Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9) = Z4)).

tff(match_enum_STATUT_E_Epuisee, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:
  A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]: (match_enum_STATUT(A, e_Epuisee, Z,
  Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9) = Z5)).

tff(match_enum_STATUT_E_Nouvel, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:
  A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]: (match_enum_STATUT(A, e_Nouvel, Z,
  Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9) = Z6)).

tff(match_enum_STATUT_E_Dernier, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:
  A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]: (match_enum_STATUT(A, e_Dernier, Z,
  Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9) = Z7)).

tff(match_enum_STATUT_E_Hors_delai, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_STATUT(A, e_Hors_delai, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z8)).

tff(match_enum_STATUT_E_Incident, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_STATUT(A, e_Incident, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z9)).

tff(e_Valide_E_Invalide, axiom, ~ (e_Valide = e_Invalide)).

tff(e_Valide_E_Illisible, axiom, ~ (e_Valide = e_Illisible)).

tff(e_Valide_E_Interdite, axiom, ~ (e_Valide = e_Interdite)).

tff(e_Valide_E_Perimee, axiom, ~ (e_Valide = e_Perimee)).

tff(e_Valide_E_Epuisee, axiom, ~ (e_Valide = e_Epuisee)).

tff(e_Valide_E_Nouvel, axiom, ~ (e_Valide = e_Nouvel)).

tff(e_Valide_E_Dernier, axiom, ~ (e_Valide = e_Dernier)).

tff(e_Valide_E_Hors_delai, axiom, ~ (e_Valide = e_Hors_delai)).

tff(e_Valide_E_Incident, axiom, ~ (e_Valide = e_Incident)).

tff(e_Invalide_E_Illisible, axiom, ~ (e_Invalide = e_Illisible)).

tff(e_Invalide_E_Interdite, axiom, ~ (e_Invalide = e_Interdite)).

tff(e_Invalide_E_Perimee, axiom, ~ (e_Invalide = e_Perimee)).

tff(e_Invalide_E_Epuisee, axiom, ~ (e_Invalide = e_Epuisee)).

tff(e_Invalide_E_Nouvel, axiom, ~ (e_Invalide = e_Nouvel)).

tff(e_Invalide_E_Dernier, axiom, ~ (e_Invalide = e_Dernier)).

tff(e_Invalide_E_Hors_delai, axiom, ~ (e_Invalide = e_Hors_delai)).

tff(e_Invalide_E_Incident, axiom, ~ (e_Invalide = e_Incident)).

tff(e_Illisible_E_Interdite, axiom, ~ (e_Illisible = e_Interdite)).

tff(e_Illisible_E_Perimee, axiom, ~ (e_Illisible = e_Perimee)).

tff(e_Illisible_E_Epuisee, axiom, ~ (e_Illisible = e_Epuisee)).

tff(e_Illisible_E_Nouvel, axiom, ~ (e_Illisible = e_Nouvel)).

tff(e_Illisible_E_Dernier, axiom, ~ (e_Illisible = e_Dernier)).

tff(e_Illisible_E_Hors_delai, axiom, ~ (e_Illisible = e_Hors_delai)).

tff(e_Illisible_E_Incident, axiom, ~ (e_Illisible = e_Incident)).

tff(e_Interdite_E_Perimee, axiom, ~ (e_Interdite = e_Perimee)).

tff(e_Interdite_E_Epuisee, axiom, ~ (e_Interdite = e_Epuisee)).

tff(e_Interdite_E_Nouvel, axiom, ~ (e_Interdite = e_Nouvel)).

tff(e_Interdite_E_Dernier, axiom, ~ (e_Interdite = e_Dernier)).

tff(e_Interdite_E_Hors_delai, axiom, ~ (e_Interdite = e_Hors_delai)).

tff(e_Interdite_E_Incident, axiom, ~ (e_Interdite = e_Incident)).

tff(e_Perimee_E_Epuisee, axiom, ~ (e_Perimee = e_Epuisee)).

tff(e_Perimee_E_Nouvel, axiom, ~ (e_Perimee = e_Nouvel)).

tff(e_Perimee_E_Dernier, axiom, ~ (e_Perimee = e_Dernier)).

tff(e_Perimee_E_Hors_delai, axiom, ~ (e_Perimee = e_Hors_delai)).

tff(e_Perimee_E_Incident, axiom, ~ (e_Perimee = e_Incident)).

tff(e_Epuisee_E_Nouvel, axiom, ~ (e_Epuisee = e_Nouvel)).

tff(e_Epuisee_E_Dernier, axiom, ~ (e_Epuisee = e_Dernier)).

tff(e_Epuisee_E_Hors_delai, axiom, ~ (e_Epuisee = e_Hors_delai)).

tff(e_Epuisee_E_Incident, axiom, ~ (e_Epuisee = e_Incident)).

tff(e_Nouvel_E_Dernier, axiom, ~ (e_Nouvel = e_Dernier)).

tff(e_Nouvel_E_Hors_delai, axiom, ~ (e_Nouvel = e_Hors_delai)).

tff(e_Nouvel_E_Incident, axiom, ~ (e_Nouvel = e_Incident)).

tff(e_Dernier_E_Hors_delai, axiom, ~ (e_Dernier = e_Hors_delai)).

tff(e_Dernier_E_Incident, axiom, ~ (e_Dernier = e_Incident)).

tff(e_Hors_delai_E_Incident, axiom, ~ (e_Hors_delai = e_Incident)).

tff(enum_STATUT_inversion, axiom, ![U:enum_STATUT]: ((((((((((U = e_Valide)
  | (U = e_Invalide)) | (U = e_Illisible)) | (U = e_Interdite))
  | (U = e_Perimee)) | (U = e_Epuisee)) | (U = e_Nouvel)) | (U = e_Dernier))
  | (U = e_Hors_delai)) | (U = e_Incident))).

tff(set_enum_STATUT, type, set_enum_STATUT: set(enum_STATUT)).

tff(set_enum_STATUT_axiom, axiom, ![X:enum_STATUT]: mem(enum_STATUT, X,
  set_enum_STATUT)).

tff(f1, type, f1: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f1_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f1(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((((($true & $true)
  & $true) & $true) & $true) & $true) & $true))).

tff(f2, type, f2: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f2_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f2(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> ((((((($true & $true)
  & mem($int, V_csomdelai_1, integer)) & $lesseq(0,V_csomdelai_1))
  & $lesseq(V_csomdelai_1,2147483647)) & $true)
  & ((V_csomfin_delai_1 = false) => $lesseq(1,V_csomdelai_1)))
  & ($lesseq(1,V_csomdelai_1) => (V_csomfin_delai_1 = false))))).

tff(f3, type, f3: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f3_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f3(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> ($true & mem($int, 0,
  integer)))).

tff(f6, type, f6: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f6_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f6(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> ((((((($true
  & mem($int, V_somme_1, mk(100, 900))) & $true)
  & mem($int, V_somme_maximum_1, mk(100, 900))) & $true)
  & (V_etat_cls = V_b_etat_cls_1)) & (V_somme = V_somme_1))
  & (V_somme_maximum = V_somme_maximum_1)))).

tff(f8, type, f8: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f8_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f8(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (($true
  & mem($int, V_som_max, mk(100, 900))) & (V_etat_cls = false)))).

tff(f9, type, f9: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f9_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f9(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (($true
  & mem($int, V_som_max, mk(100, 900))) & (V_etat_cls = false)))).

tff(f15, type, f15: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f15_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f15(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> ($true
  & (V_etat_cls = true)))).

tff(f16, type, f16: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f16_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f16(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((((($true
  & (V_etat_cls = true)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)))).

tff(f18, type, f18: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f18_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f18(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> ((((((((($true
  & (V_etat_cls = true)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))))).

tff(f19, type, f19: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f19_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f19(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> mem($int, $difference(V_delai_0,1), integer))).

tff(f20, type, f20: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f20_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f20(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> $lesseq(0,$difference(V_delai_0,1)))).

tff(f21, type, f21: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f21_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f21(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((((((((($true
  & (V_etat_cls = true)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & (V_fin = false)))).

tff(f22, type, f22: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f22_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f22(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> $lesseq(1,$difference(V_delai_0,1)))).

tff(f23, type, f23: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f23_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f23(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((((((((($true
  & (V_etat_cls = true)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false)))
  & $lesseq(1,$difference(V_delai_0,1))))).

tff(f25, type, f25: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f25_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f25(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)))).

tff(f27, type, f27: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f27_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f27(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true))).

tff(f29, type, f29: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f29_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f29(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & (V_rsl = true))
  & $lesseq($sum(V_somme_maximum_1,1),V_som)))).

tff(f30, type, f30: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f30_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f30(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> $lesseq($sum($difference(V_csomdelai_2,1),1),V_csomdelai_2))).

tff(f31, type, f31: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f31_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f31(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> mem($int, $difference(V_csomdelai_2,1), integer))).

tff(f32, type, f32: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f32_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f32(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> $lesseq(0,$difference(V_csomdelai_2,1)))).

tff(f33, type, f33: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f33_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f33(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & (V_rsl = true))
  & $lesseq($sum(V_somme_maximum_1,1),V_som)) & (V_fin_0 = false)))).

tff(f34, type, f34: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f34_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f34(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> $lesseq(1,$difference(V_csomdelai_2,1)))).

tff(f35, type, f35: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f35_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f35(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & (V_rsl = true))
  & $lesseq($sum(V_somme_maximum_1,1),V_som))
  & $lesseq(1,$difference(V_csomdelai_2,1))))).

tff(f37, type, f37: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f37_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f37(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & ((V_rsl = true) => ~
  $lesseq($sum(V_somme_maximum_1,1),V_som))))).

tff(f38, type, f38: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f38_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f38(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & ((V_rsl = true) => ~
  $lesseq($sum(V_somme_maximum_1,1),V_som))) & (V_rsl = true)))).

tff(f39, type, f39: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f39_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f39(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> mem($int, V_som,
  mk(100, V_somme_maximum_1)))).

tff(f40, type, f40: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f40_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f40(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & ((V_rsl = true) => ~
  $lesseq($sum(V_somme_maximum_1,1),V_som))) & (V_fin_0 = false)))).

tff(f41, type, f41: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f41_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f41(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((((((((((((((((($true & (V_etat_cls = true)) & $true)
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & $true) & $true) & $true) & mem($int, V_csomdelai_2,
  integer)) & $lesseq(0,V_csomdelai_2)) & ((V_val_0 = true)
  => mem($int, V_som_brt_0, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delai_2 = false) => $lesseq(1,V_csomdelai_2)))
  & ($lesseq(1,V_csomdelai_2) => (V_csomfin_delai_2 = false)))
  & (V_fin_del_0 = V_csomfin_delai_2)) & (V_fin_del_0 = false))
  & (V_val_0 = false)) & (V_ii_0 = false)) & $true) & mem($int, V_som,
  integer)) & $lesseq(0,V_som)) & $lesseq(V_som,2147483647))
  & ((V_rsl = true) => mem($int, V_som, mk(100, 900)))) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_csomdelai_2)))
  & ($lesseq(2,V_csomdelai_2) => (V_fin_0 = false))) & ((V_rsl = true) => ~
  $lesseq($sum(V_somme_maximum_1,1),V_som)))
  & $lesseq(1,$difference(V_csomdelai_2,1))))).

tff(f42, type, f42: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f42_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f42(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((((($true & (V_etat_cls = true)) & $true) & ~
  (((V_val_7777 = false) & (V_ii_7777 = false))
  & (V_csomfin_delaiz_7778 = false))) & $true) & $true) & $true)
  & mem($int, V_csomdelaiz_7778, integer)) & $lesseq(0,V_csomdelaiz_7778))
  & ((V_val_7777 = true) => mem($int, V_som_brt_7777, mk(100,
  V_somme_maximum_1)))) & ((V_csomfin_delaiz_7778 = false)
  => $lesseq(1,V_csomdelaiz_7778))) & ($lesseq(1,V_csomdelaiz_7778)
  => (V_csomfin_delaiz_7778 = false))) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & ~ (V_ii_7777 = true)) & ~
  (V_val_7777 = false)))).

tff(f46, type, f46: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f46_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f46(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((($true & (V_etat_cls = true)) & $true) & $true)
  & $true) & mem($int, V_csomdelaiz_7778, integer))
  & $lesseq(0,V_csomdelaiz_7778)) & ((V_val_7777 = true)
  => mem($int, V_som_brt_7777, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delaiz_7778 = false) => $lesseq(1,V_csomdelaiz_7778)))
  & ($lesseq(1,V_csomdelaiz_7778) => (V_csomfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & mem($int, 0, integer)))).

tff(f48, type, f48: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f48_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f48(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((($true & (V_etat_cls = true)) & $true) & $true)
  & $true) & mem($int, V_csomdelaiz_7778, integer))
  & $lesseq(0,V_csomdelaiz_7778)) & ((V_val_7777 = true)
  => mem($int, V_som_brt_7777, mk(100, V_somme_maximum_1))))
  & ((V_csomfin_delaiz_7778 = false) => $lesseq(1,V_csomdelaiz_7778)))
  & ($lesseq(1,V_csomdelaiz_7778) => (V_csomfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & mem($int, 0, integer)) & (e_Incident = e_Valide)))).

tff(f50, type, f50: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f50_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f50(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> (((((((((((((((((($true & (V_etat_cls = true)) & $true) & ~
  ((V_ii_7777 = false) & (V_csomfin_delaiz_7778 = false))) & $true) & $true)
  & mem($int, V_csomdelaiz_7778, integer)) & $lesseq(0,V_csomdelaiz_7778))
  & ((V_csomfin_delaiz_7778 = false) => $lesseq(1,V_csomdelaiz_7778)))
  & ($lesseq(1,V_csomdelaiz_7778) => (V_csomfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & ~ (V_ii_7777 = true)) & mem($int, 0, integer)))).

tff(f53, type, f53: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f53_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f53(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((($true & (V_etat_cls = true)) & $true) & ~
  ((V_ii_7777 = false) & (V_csomfin_delaiz_7778 = false))) & $true) & $true)
  & mem($int, V_csomdelaiz_7778, integer)) & $lesseq(0,V_csomdelaiz_7778))
  & ((V_csomfin_delaiz_7778 = false) => $lesseq(1,V_csomdelaiz_7778)))
  & ($lesseq(1,V_csomdelaiz_7778) => (V_csomfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & ~ (V_ii_7777 = true)) & mem($int, 0, integer))
  & (e_Hors_delai = e_Valide)))).

tff(f54, type, f54: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f54_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f54(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  <=> ((((((((((((((((((((($true & (V_etat_cls = true)) & $true) & ~
  (((V_val_7777 = false) & (V_ii_7777 = false))
  & (V_csomfin_delaiz_7778 = false))) & $true) & $true) & $true)
  & mem($int, V_csomdelaiz_7778, integer)) & $lesseq(0,V_csomdelaiz_7778))
  & ((V_val_7777 = true) => mem($int, V_som_brt_7777, mk(100,
  V_somme_maximum_1)))) & ((V_csomfin_delaiz_7778 = false)
  => $lesseq(1,V_csomdelaiz_7778))) & ($lesseq(1,V_csomdelaiz_7778)
  => (V_csomfin_delaiz_7778 = false))) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & ~ (V_ii_7777 = true)) & ~
  (V_val_7777 = false)) & mem($int, 0, integer)))).

tff(f58, type, f58: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f58_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f58(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((($true
  & mem($int, V_cse, integer)) & $lesseq(0,V_cse))
  & $lesseq(V_cse,2147483647)) & (V_etat_cls = false)))).

tff(f59, type, f59: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f59_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f59(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((((($true
  & mem($int, V_cse, integer)) & $lesseq(0,V_cse))
  & $lesseq(V_cse,2147483647)) & (V_etat_cls = false)) & $true)
  & $lesseq(V_somme_1,V_cse)))).

tff(f61, type, f61: (bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * bool * bool * bool *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  bool * bool) > $o).

tff(f61_def, axiom, ![V_val_7777:bool, V_val_0:bool, V_tst_cls_0:bool,
  V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:$int, V_somme:$int,
  V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int, V_som:$int, V_rsl:
  bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:
  bool, V_etat_cls:bool, V_delai_0:$int, V_csomfin_delaiz_7778:bool,
  V_csomfin_delai_2:bool, V_csomfin_delai_1:bool, V_csomfin_delai:bool,
  V_csomdelaiz_7778:$int, V_csomdelai_2:$int, V_csomdelai_1:$int,
  V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool, V_b_etat_cls:bool]:
  (f61(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) <=> (((((($true
  & mem($int, V_cse, integer)) & $lesseq(0,V_cse))
  & $lesseq(V_cse,2147483647)) & (V_etat_cls = false)) & $true) & ~
  $lesseq(V_somme_1,V_cse)))).

tff(lecture_somme_14, conjecture, ![V_val_7777:bool, V_val_0:bool,
  V_tst_cls_0:bool, V_somme_maximum_1:$int, V_somme_maximum:$int, V_somme_1:
  $int, V_somme:$int, V_som_max:$int, V_som_brt_7777:$int, V_som_brt_0:$int,
  V_som:$int, V_rsl:bool, V_ii_7777:bool, V_ii_0:bool, V_fin_del_0:bool,
  V_fin_0:bool, V_fin:bool, V_etat_cls:bool, V_delai_0:$int,
  V_csomfin_delaiz_7778:bool, V_csomfin_delai_2:bool, V_csomfin_delai_1:bool,
  V_csomfin_delai:bool, V_csomdelaiz_7778:$int, V_csomdelai_2:$int,
  V_csomdelai_1:$int, V_csomdelai:$int, V_cse:$int, V_b_etat_cls_1:bool,
  V_b_etat_cls:bool]: ((f1(V_val_7777, V_val_0, V_tst_cls_0,
  V_somme_maximum_1, V_somme_maximum, V_somme_1, V_somme, V_som_max,
  V_som_brt_7777, V_som_brt_0, V_som, V_rsl, V_ii_7777, V_ii_0, V_fin_del_0,
  V_fin_0, V_fin, V_etat_cls, V_delai_0, V_csomfin_delaiz_7778,
  V_csomfin_delai_2, V_csomfin_delai_1, V_csomfin_delai, V_csomdelaiz_7778,
  V_csomdelai_2, V_csomdelai_1, V_csomdelai, V_cse, V_b_etat_cls_1,
  V_b_etat_cls) & (f2(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1,
  V_somme_maximum, V_somme_1, V_somme, V_som_max, V_som_brt_7777,
  V_som_brt_0, V_som, V_rsl, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_etat_cls, V_delai_0, V_csomfin_delaiz_7778, V_csomfin_delai_2,
  V_csomfin_delai_1, V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2,
  V_csomdelai_1, V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  & (f6(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1, V_somme_maximum,
  V_somme_1, V_somme, V_som_max, V_som_brt_7777, V_som_brt_0, V_som, V_rsl,
  V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin, V_etat_cls, V_delai_0,
  V_csomfin_delaiz_7778, V_csomfin_delai_2, V_csomfin_delai_1,
  V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2, V_csomdelai_1,
  V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls) & ($true
  & (f15(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1,
  V_somme_maximum, V_somme_1, V_somme, V_som_max, V_som_brt_7777,
  V_som_brt_0, V_som, V_rsl, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_etat_cls, V_delai_0, V_csomfin_delaiz_7778, V_csomfin_delai_2,
  V_csomfin_delai_1, V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2,
  V_csomdelai_1, V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  & (f37(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1,
  V_somme_maximum, V_somme_1, V_somme, V_som_max, V_som_brt_7777,
  V_som_brt_0, V_som, V_rsl, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_etat_cls, V_delai_0, V_csomfin_delaiz_7778, V_csomfin_delai_2,
  V_csomfin_delai_1, V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2,
  V_csomdelai_1, V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  & $true)))))) => (f31(V_val_7777, V_val_0, V_tst_cls_0, V_somme_maximum_1,
  V_somme_maximum, V_somme_1, V_somme, V_som_max, V_som_brt_7777,
  V_som_brt_0, V_som, V_rsl, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_etat_cls, V_delai_0, V_csomfin_delaiz_7778, V_csomfin_delai_2,
  V_csomfin_delai_1, V_csomfin_delai, V_csomdelaiz_7778, V_csomdelai_2,
  V_csomdelai_1, V_csomdelai, V_cse, V_b_etat_cls_1, V_b_etat_cls)
  & $true))).
