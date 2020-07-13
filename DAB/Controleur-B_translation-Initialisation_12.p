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

tff(f1, type, f1: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f1_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f1(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (((((($true & $true) & $true) & $true) & $true) & $true)
  & $true))).

tff(f2, type, f2: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f2_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f2(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Traitement_code))
  & (e_Hors_service = e_En_service)))).

tff(f6, type, f6: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f6_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f6(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Traitement_code))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Traitement_carte)))).

tff(f8, type, f8: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f8_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f8(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Restitution_carte))
  & (e_Hors_service = e_En_service)))).

tff(f11, type, f11: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f11_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f11(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Traitement_carte)))).

tff(f13, type, f13: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f13_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f13(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Traitement_code)))).

tff(f15, type, f15: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f15_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f15(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Traitement_somme)))).

tff(f17, type, f17: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f17_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f17(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (e_Hors_service = e_En_service))
  & (e_Veille = e_Distribution_billets)))).

tff(f19, type, f19: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f19_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f19(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)))).

tff(f22, type, f22: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f22_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f22(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Traitement_carte)))).

tff(f24, type, f24: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f24_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f24(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Traitement_code)))).

tff(f26, type, f26: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f26_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f26(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)) & (e_Veille = e_Restitution_carte)))).

tff(f28, type, f28: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f28_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f28(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((((((((((($true & $true) & $true) & $true) & $true)
  & $true) & $true) & (((V_panne_dab = true) | (V_caisse_vde = true))
  => (V_etat_dab = e_Hors_service))) & ((V_etat_dab = e_Hors_service)
  => ((V_panne_dab = true) | (V_caisse_vde = true))))
  & (((V_courant = e_Traitement_code) & (V_etat_dab = e_En_service))
  => ((mem(enum_ETAT_AUTOMATE, V_precedent,
  union(enum_ETAT_AUTOMATE, singleton(enum_ETAT_AUTOMATE, e_Traitement_code),
  singleton(enum_ETAT_AUTOMATE, e_Traitement_carte)))
  & ((V_precedent = e_Traitement_code) => mem(enum_STATUT, V_resultat,
  union(enum_STATUT, singleton(enum_STATUT, e_Nouvel),
  singleton(enum_STATUT, e_Dernier))))) & ((V_precedent = e_Traitement_carte)
  => (V_resultat = e_Valide))))) & (((V_courant = e_Restitution_carte)
  & (V_etat_dab = e_En_service)) => ((((mem(enum_ETAT_AUTOMATE, V_precedent,
  union(enum_ETAT_AUTOMATE, union(enum_ETAT_AUTOMATE, union(enum_ETAT_AUTOMATE, singleton(enum_ETAT_AUTOMATE, e_Traitement_carte),
  singleton(enum_ETAT_AUTOMATE, e_Traitement_code)),
  singleton(enum_ETAT_AUTOMATE, e_Traitement_somme)),
  singleton(enum_ETAT_AUTOMATE, e_Distribution_billets)))
  & ((V_precedent = e_Traitement_carte) => mem(enum_STATUT, V_resultat,
  union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Perimee),
  singleton(enum_STATUT, e_Epuisee)), singleton(enum_STATUT, e_Illisible)),
  singleton(enum_STATUT, e_Invalide))))) & ((V_precedent = e_Traitement_code)
  => mem(enum_STATUT, V_resultat,
  union(enum_STATUT, singleton(enum_STATUT, e_Hors_delai),
  singleton(enum_STATUT, e_Incident)))))
  & ((V_precedent = e_Traitement_somme) => mem(enum_STATUT, V_resultat,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Invalide),
  singleton(enum_STATUT, e_Hors_delai)),
  singleton(enum_STATUT, e_Incident)))))
  & ((V_precedent = e_Distribution_billets) => mem(enum_STATUT, V_resultat,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Hors_delai)),
  singleton(enum_STATUT, e_Incident)))))))
  & (((V_courant = e_Confiscation_carte) & (V_etat_dab = e_En_service))
  => (((mem(enum_ETAT_AUTOMATE, V_precedent,
  union(enum_ETAT_AUTOMATE, union(enum_ETAT_AUTOMATE, singleton(enum_ETAT_AUTOMATE, e_Traitement_carte),
  singleton(enum_ETAT_AUTOMATE, e_Traitement_code)),
  singleton(enum_ETAT_AUTOMATE, e_Restitution_carte)))
  & ((V_precedent = e_Traitement_carte) => (V_resultat = e_Interdite)))
  & ((V_precedent = e_Traitement_code) => (V_resultat = e_Invalide)))
  & ((V_precedent = e_Restitution_carte) => mem(enum_STATUT, V_resultat,
  union(enum_STATUT, singleton(enum_STATUT, e_Incident),
  singleton(enum_STATUT, e_Hors_delai))))))))).

tff(f29, type, f29: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f29_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f29(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ($true & (e_En_service = e_Hors_service)))).

tff(f32, type, f32: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f32_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f32(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ($true & (e_Veille = e_Traitement_code)))).

tff(f35, type, f35: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f35_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f35(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Traitement_code))
  & (e_Veille = e_Traitement_carte)))).

tff(f37, type, f37: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f37_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f37(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ($true & (e_Veille = e_Restitution_carte)))).

tff(f39, type, f39: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f39_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f39(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Restitution_carte))
  & (e_Veille = e_Traitement_carte)))).

tff(f41, type, f41: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f41_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f41(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Restitution_carte))
  & (e_Veille = e_Traitement_code)))).

tff(f43, type, f43: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f43_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f43(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Restitution_carte))
  & (e_Veille = e_Traitement_somme)))).

tff(f45, type, f45: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f45_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f45(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Restitution_carte))
  & (e_Veille = e_Distribution_billets)))).

tff(f47, type, f47: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f47_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f47(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ($true & (e_Veille = e_Confiscation_carte)))).

tff(f49, type, f49: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f49_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f49(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Confiscation_carte))
  & (e_Veille = e_Traitement_carte)))).

tff(f51, type, f51: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f51_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f51(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Confiscation_carte))
  & (e_Veille = e_Traitement_code)))).

tff(f53, type, f53: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f53_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f53(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Confiscation_carte))
  & (e_Veille = e_Restitution_carte)))).

tff(f55, type, f55: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f55_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f55(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & $true) & $true) & ((V_tst_dab = true)
  | (V_cse_vde = true))))).

tff(f56, type, f56: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f56_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f56(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (V_courant = e_Traitement_code))
  & (e_Hors_service = e_En_service)))).

tff(f58, type, f58: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f58_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f58(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Traitement_code))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_code)))).

tff(f60, type, f60: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f60_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f60(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Traitement_code))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_carte)))).

tff(f62, type, f62: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f62_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f62(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (V_courant = e_Restitution_carte))
  & (e_Hors_service = e_En_service)))).

tff(f64, type, f64: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f64_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f64(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Restitution_carte))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_carte)))).

tff(f66, type, f66: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f66_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f66(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Restitution_carte))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_code)))).

tff(f68, type, f68: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f68_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f68(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Restitution_carte))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_somme)))).

tff(f70, type, f70: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f70_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f70(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Restitution_carte))
  & (e_Hors_service = e_En_service))
  & (V_precedent = e_Distribution_billets)))).

tff(f72, type, f72: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f72_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f72(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (V_courant = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)))).

tff(f74, type, f74: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f74_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f74(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_carte)))).

tff(f76, type, f76: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f76_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f76(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Confiscation_carte))
  & (e_Hors_service = e_En_service)) & (V_precedent = e_Traitement_code)))).

tff(f78, type, f78: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f78_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f78(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (V_courant = e_Confiscation_carte))
  & (e_Hors_service = e_En_service))
  & (V_precedent = e_Restitution_carte)))).

tff(f80, type, f80: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f80_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f80(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ($true & (V_etat_dab = e_Hors_service)))).

tff(f81, type, f81: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f81_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f81(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Traitement_code))
  & (V_etat_dab = e_En_service)))).

tff(f83, type, f83: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f83_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f83(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Traitement_code))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_code)))).

tff(f84, type, f84: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f84_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f84(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Traitement_code))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_carte)))).

tff(f85, type, f85: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f85_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f85(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Restitution_carte))
  & (V_etat_dab = e_En_service)))).

tff(f87, type, f87: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f87_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f87(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_carte)))).

tff(f88, type, f88: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f88_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f88(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_code)))).

tff(f89, type, f89: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f89_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f89(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_somme)))).

tff(f90, type, f90: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f90_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f90(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Restitution_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Distribution_billets)))).

tff(f91, type, f91: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f91_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f91(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (($true & (e_Veille = e_Confiscation_carte))
  & (V_etat_dab = e_En_service)))).

tff(f93, type, f93: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f93_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f93(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Confiscation_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_carte)))).

tff(f94, type, f94: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f94_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f94(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Confiscation_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Traitement_code)))).

tff(f95, type, f95: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f95_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f95(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((($true & (e_Veille = e_Confiscation_carte))
  & (V_etat_dab = e_En_service)) & (V_courant = e_Restitution_carte)))).

tff(f96, type, f96: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f96_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f96(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((((((((($true & (V_etat_dab = e_En_service))
  & (V_panne_dab = false)) & (V_caisse_vde = false)) & $true)
  & ((V_courant = e_Traitement_carte) => mem(enum_STATUT, V_rslt,
  union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Illisible)),
  singleton(enum_STATUT, e_Perimee)), singleton(enum_STATUT, e_Interdite)),
  singleton(enum_STATUT, e_Incident)), singleton(enum_STATUT, e_Epuisee)))))
  & ((V_courant = e_Traitement_code) => mem(enum_STATUT, V_rslt,
  union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Nouvel)),
  singleton(enum_STATUT, e_Dernier)), singleton(enum_STATUT, e_Hors_delai)),
  singleton(enum_STATUT, e_Incident))))) & ((V_courant = e_Traitement_somme)
  => mem(enum_STATUT, V_rslt,
  union(enum_STATUT, union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Hors_delai)),
  singleton(enum_STATUT, e_Incident)))))
  & (mem(enum_ETAT_AUTOMATE, V_courant,
  union(enum_ETAT_AUTOMATE, union(enum_ETAT_AUTOMATE, singleton(enum_ETAT_AUTOMATE, e_Distribution_billets),
  singleton(enum_ETAT_AUTOMATE, e_Restitution_carte)),
  singleton(enum_ETAT_AUTOMATE, e_Veille))) => mem(enum_STATUT, V_rslt,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Hors_delai)),
  singleton(enum_STATUT, e_Incident)))))
  & ((V_courant = e_Confiscation_carte) => mem(enum_STATUT, V_rslt,
  union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide))))))).

tff(f97, type, f97: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f97_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f97(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> ((((((((($true & $true) & ((V_courant = e_Veille)
  => ((((V_rslt = e_Valide) => (V_etat = e_Traitement_carte))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Veille)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille)))))
  & ((V_courant = e_Traitement_carte) => ((((((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_code)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Illisible)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Interdite)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Perimee)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Traitement_code)))).

tff(f98, type, f98: (bool * enum_STATUT * enum_STATUT * enum_ETAT_AUTOMATE *
  bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool * enum_ETAT_AUTOMATE *
  bool) > $o).

tff(f98_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f98(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) <=> (((((((((($true & $true) & ((V_courant = e_Veille)
  => ((((V_rslt = e_Valide) => (V_etat = e_Traitement_carte))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Veille)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille)))))
  & ((V_courant = e_Traitement_carte) => ((((((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_code)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Illisible)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Interdite)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Perimee)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Traitement_code)) & (V_courant = e_Traitement_code)))).

tff(f100, type, f100: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f100_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f100(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Traitement_code)) & (V_courant = e_Traitement_carte)))).

tff(f102, type, f102: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f102_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f102(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> ((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Restitution_carte)))).

tff(f103, type, f103: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f103_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f103(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Restitution_carte)) & (V_courant = e_Traitement_carte)))).

tff(f105, type, f105: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f105_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f105(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Restitution_carte)) & (V_courant = e_Traitement_code)))).

tff(f107, type, f107: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f107_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f107(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Restitution_carte)) & (V_courant = e_Traitement_somme)))).

tff(f109, type, f109: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f109_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f109(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Restitution_carte))
  & (V_courant = e_Distribution_billets)))).

tff(f111, type, f111: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f111_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f111(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> ((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Confiscation_carte)))).

tff(f112, type, f112: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f112_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f112(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Confiscation_carte)) & (V_courant = e_Traitement_carte)))).

tff(f114, type, f114: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f114_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f114(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Confiscation_carte)) & (V_courant = e_Traitement_code)))).

tff(f116, type, f116: (bool * enum_STATUT * enum_STATUT *
  enum_ETAT_AUTOMATE * bool * enum_ETAT_DAB * enum_ETAT_AUTOMATE * bool *
  enum_ETAT_AUTOMATE * bool) > $o).

tff(f116_def, axiom, ![V_tst_dab:bool, V_rslt:enum_STATUT, V_resultat:
  enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool, V_etat_dab:
  enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool, V_courant:
  enum_ETAT_AUTOMATE, V_caisse_vde:bool]: (f116(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) <=> (((((((((($true & $true)
  & ((V_courant = e_Veille) => ((((V_rslt = e_Valide)
  => (V_etat = e_Traitement_carte)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Veille))) & ((V_rslt = e_Incident)
  => (V_etat = e_Veille))))) & ((V_courant = e_Traitement_carte)
  => ((((((((V_rslt = e_Valide) => (V_etat = e_Traitement_code))
  & ((V_rslt = e_Invalide) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Illisible) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Interdite) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Perimee) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Veille))) & ((V_rslt = e_Epuisee)
  => (V_etat = e_Restitution_carte))))) & ((V_courant = e_Traitement_code)
  => (((((((V_rslt = e_Valide) => (V_etat = e_Traitement_somme))
  & ((V_rslt = e_Invalide) => (V_etat = e_Confiscation_carte)))
  & ((V_rslt = e_Nouvel) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Dernier) => (V_etat = e_Traitement_code)))
  & ((V_rslt = e_Hors_delai) => (V_etat = e_Restitution_carte)))
  & ((V_rslt = e_Incident) => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Traitement_somme) => (((((V_rslt = e_Valide)
  => (V_etat = e_Distribution_billets)) & ((V_rslt = e_Invalide)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Restitution_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Restitution_carte)))))
  & ((V_courant = e_Distribution_billets) => (V_etat = e_Restitution_carte)))
  & ((V_courant = e_Restitution_carte) => ((((V_rslt = e_Valide)
  => (V_etat = e_Veille)) & ((V_rslt = e_Hors_delai)
  => (V_etat = e_Confiscation_carte))) & ((V_rslt = e_Incident)
  => (V_etat = e_Confiscation_carte)))))
  & ((V_courant = e_Confiscation_carte) => (V_etat = e_Veille)))
  & (V_etat = e_Confiscation_carte)) & (V_courant = e_Restitution_carte)))).

tff(initialisation_12, conjecture, ![V_tst_dab:bool, V_rslt:enum_STATUT,
  V_resultat:enum_STATUT, V_precedent:enum_ETAT_AUTOMATE, V_panne_dab:bool,
  V_etat_dab:enum_ETAT_DAB, V_etat:enum_ETAT_AUTOMATE, V_cse_vde:bool,
  V_courant:enum_ETAT_AUTOMATE, V_caisse_vde:bool]: ((f1(V_tst_dab, V_rslt,
  V_resultat, V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde,
  V_courant, V_caisse_vde) & ($true & (f26(V_tst_dab, V_rslt, V_resultat,
  V_precedent, V_panne_dab, V_etat_dab, V_etat, V_cse_vde, V_courant,
  V_caisse_vde) & $true))) => (mem(enum_STATUT, e_Incident,
  union(enum_STATUT, singleton(enum_STATUT, e_Incident),
  singleton(enum_STATUT, e_Hors_delai))) & $true))).
