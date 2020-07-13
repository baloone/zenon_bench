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

tff(f1, type, f1: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f1_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f1(V_val_0, V_tst_lct_0, V_sld, V_pre_7777,
  V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1, V_lisible,
  V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((((((($true & $true)
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_D_min, integer))
  & $lesseq(0,V_D_min)) & $lesseq(V_D_min,2147483647)) & mem($int, V_D_max,
  integer)) & $lesseq(0,V_D_max)) & $lesseq(V_D_max,2147483647))
  & $lesseq($sum(V_D_min,1),V_D_max)) & infix_eqeq($int, V_DATE, mk(V_D_min,
  V_D_max))) & mem($int, V_K0, V_CARTE)) & mem($int, V_HS, V_CARTE)) & ~
  (V_K0 = V_HS)) & mem(set($int), V_CARTE, finite_subsets($int, integer)))
  & ~ infix_eqeq($int, V_CARTE, empty($int))))).

tff(f2, type, f2: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f2_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f2(V_val_0, V_tst_lct_0, V_sld, V_pre_7777,
  V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1, V_lisible,
  V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((($true
  & mem($int, V_date, V_DATE)) & mem(set($int), V_clients,
  power($int, diff($int, V_CARTE, union($int, singleton($int, V_K0),
  singleton($int, V_HS)))))) & mem(set(tuple2($int, $int)), V_comptes,
  infix_plmngt($int, $int, V_clients, nat))) & infix_eqeq($int, dom($int,
  $int, V_comptes), V_clients)) & mem(set($int), V_interdits,
  power($int, V_clients))) & $true) & $true) & $true)
  & ((V_b_carte_1 = false) => (V_b_verrous_1 = false)))
  & mem($int, V_lectdelai_1, integer)) & $lesseq(0,V_lectdelai_1))
  & $lesseq(V_lectdelai_1,2147483647)) & $true)
  & ((V_lectfin_delai_1 = false) => $lesseq(1,V_lectdelai_1)))
  & ($lesseq(1,V_lectdelai_1) => (V_lectfin_delai_1 = false))))).

tff(f5, type, f5: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f5_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f5(V_val_0, V_tst_lct_0, V_sld, V_pre_7777,
  V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1, V_lisible,
  V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & mem($int, 0, integer)))).

tff(f10, type, f10: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f10_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f10(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((($true & $true)
  & mem($int, V_carte_1, V_CARTE)) & mem($int, V_cde_carte_1, mk(0, 9999)))
  & mem($int, V_date_validite_1, V_DATE)) & $true) & ((V_carte_1 = V_K0)
  => (V_b_carte_1 = false))) & ((V_b_carte_1 = false) => (V_carte_1 = V_K0)))
  & (V_lisible = V_lisible_1)) & (V_carte = V_carte_1))
  & (V_cde_carte = V_cde_carte_1))
  & (V_date_validite = V_date_validite_1)))).

tff(f13, type, f13: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f13_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f13(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & ~ (V_carte_1 = V_K0)))).

tff(f14, type, f14: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f14_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f14(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & ~ (V_carte_1 = V_K0)))).

tff(f16, type, f16: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f16_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f16(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & (V_carte_1 = V_K0)))).

tff(f17, type, f17: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f17_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f17(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((($true & (V_carte_1 = V_K0))
  & $true) & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)))).

tff(f19, type, f19: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f19_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f19(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((($true & (V_carte_1 = V_K0))
  & $true) & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))))).

tff(f20, type, f20: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f20_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f20(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> mem($int, $difference(V_delai_0,1),
  integer))).

tff(f21, type, f21: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f21_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f21(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE)
  <=> $lesseq(0,$difference(V_delai_0,1)))).

tff(f22, type, f22: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f22_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f22(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & (V_fin = false)))).

tff(f23, type, f23: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f23_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f23(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE)
  <=> $lesseq(1,$difference(V_delai_0,1)))).

tff(f24, type, f24: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f24_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f24(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false)))
  & $lesseq(1,$difference(V_delai_0,1))))).

tff(f26, type, f26: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f26_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f26(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & mem($int, V_lectdelai_2,
  integer)) & $lesseq(0,V_lectdelai_2)) & $true) & $true) & $true)
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = false)) & (V_ii_0 = false)))).

tff(f28, type, f28: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f28_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f28(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & mem($int, V_lectdelai_2,
  integer)) & $lesseq(0,V_lectdelai_2)) & $true) & $true) & $true)
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = false)) & (V_ii_0 = false)) & $true) & $true))).

tff(f30, type, f30: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f30_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f30(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & mem($int, V_lectdelai_2,
  integer)) & $lesseq(0,V_lectdelai_2)) & $true) & $true) & $true)
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = false)) & (V_ii_0 = false)) & $true) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_lectdelai_2)))
  & ($lesseq(2,V_lectdelai_2) => (V_fin_0 = false))))).

tff(f31, type, f31: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f31_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f31(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE)
  <=> $lesseq($sum($difference(V_lectdelai_2,1),1),V_lectdelai_2))).

tff(f32, type, f32: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f32_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f32(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE)
  <=> mem($int, $difference(V_lectdelai_2,1), integer))).

tff(f33, type, f33: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f33_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f33(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE)
  <=> $lesseq(0,$difference(V_lectdelai_2,1)))).

tff(f34, type, f34: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f34_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f34(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & mem($int, V_lectdelai_2,
  integer)) & $lesseq(0,V_lectdelai_2)) & $true) & $true) & $true)
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = false)) & (V_ii_0 = false)) & $true) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_lectdelai_2)))
  & ($lesseq(2,V_lectdelai_2) => (V_fin_0 = false))) & (V_fin_0 = false)))).

tff(f35, type, f35: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f35_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f35(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE)
  <=> $lesseq(1,$difference(V_lectdelai_2,1)))).

tff(f36, type, f36: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f36_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f36(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & mem($int, V_lectdelai_2,
  integer)) & $lesseq(0,V_lectdelai_2)) & $true) & $true) & $true)
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = false)) & (V_ii_0 = false)) & $true) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_lectdelai_2)))
  & ($lesseq(2,V_lectdelai_2) => (V_fin_0 = false)))
  & $lesseq(1,$difference(V_lectdelai_2,1))))).

tff(f38, type, f38: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f38_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f38(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_lectdelaiz_7778, integer))
  & $lesseq(0,V_lectdelaiz_7778)) & $true) & $true)
  & ((V_lectfin_delaiz_7778 = false) => $lesseq(1,V_lectdelaiz_7778)))
  & ($lesseq(1,V_lectdelaiz_7778) => (V_lectfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & mem($int, 0, integer)))).

tff(f41, type, f41: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f41_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f41(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & ~ ((V_ii_7777 = false)
  & (V_lectfin_delaiz_7778 = false))) & mem($int, V_lectdelaiz_7778,
  integer)) & $lesseq(0,V_lectdelaiz_7778)) & $true) & $true)
  & ((V_lectfin_delaiz_7778 = false) => $lesseq(1,V_lectdelaiz_7778)))
  & ($lesseq(1,V_lectdelaiz_7778) => (V_lectfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & ~ (V_ii_7777 = true)) & mem($int, 0, integer)))).

tff(f44, type, f44: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f44_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f44(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & ~ (((V_pre_7777 = false)
  & (V_ii_7777 = false)) & (V_lectfin_delaiz_7778 = false)))
  & mem($int, V_lectdelaiz_7778, integer)) & $lesseq(0,V_lectdelaiz_7778))
  & $true) & $true) & $true) & ((V_lectfin_delaiz_7778 = false)
  => $lesseq(1,V_lectdelaiz_7778))) & ($lesseq(1,V_lectdelaiz_7778)
  => (V_lectfin_delaiz_7778 = false))) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & ~ (V_ii_7777 = true)) & ~
  (V_pre_7777 = false)) & mem($int, 0, integer)))).

tff(f46, type, f46: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f46_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f46(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & (V_carte_1 = V_K0)))).

tff(f47, type, f47: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f47_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f47(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & (V_carte_1 = V_K0)))).

tff(f49, type, f49: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f49_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f49(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & $true) & mem($int, V_nro_carte_0,
  V_CARTE)) & ((V_pre_0 = false) => (V_nro_carte_0 = V_K0)))
  & ((V_nro_carte_0 = V_K0) => (V_pre_0 = false))) & $true)
  & mem($int, V_cdd_0, mk(0, 9999))) & mem($int, V_lmt_0, mk(V_D_min,
  V_D_max))) & (V_pre_0 = false)) & ((V_pre_0 = false)
  => (V_b_verrous_1 = false))))).

tff(f51, type, f51: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f51_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f51(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & $true) & mem($int, V_nro_carte_0,
  V_CARTE)) & ((V_pre_0 = false) => (V_nro_carte_0 = V_K0)))
  & ((V_nro_carte_0 = V_K0) => (V_pre_0 = false))) & $true)
  & mem($int, V_cdd_0, mk(0, 9999))) & mem($int, V_lmt_0, mk(V_D_min,
  V_D_max))) & ~ (V_pre_0 = false)) & ((V_pre_0 = false)
  => (V_b_verrous_1 = false))))).

tff(f53, type, f53: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f53_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f53(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (($true & ~ (V_carte_1 = V_K0))
  & (V_lisible_1 = true)))).

tff(f55, type, f55: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f55_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f55(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((($true & ~ (V_carte_1 = V_K0))
  & (V_lisible_1 = true)) & (e_Valide = e_Incident)))).

tff(f57, type, f57: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f57_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f57(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((($true & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = true))) & ~ (V_carte_1 = V_K0))
  & (V_lisible_1 = false)))).

tff(f59, type, f59: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f59_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f59(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((($true & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = true))) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = false))
  & (e_Illisible = e_Valide)))).

tff(f61, type, f61: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f61_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f61(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((($true & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = true))) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = false))
  & (e_Illisible = e_Incident)))).

tff(f62, type, f62: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f62_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f62(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (($true & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = true))) & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = false))))).

tff(f64, type, f64: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f64_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f64(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((($true & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = true))) & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = false))) & (e_Incident = e_Valide)))).

tff(f65, type, f65: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f65_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f65(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ~ (V_carte_1 = V_K0))).

tff(f66, type, f66: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f66_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f66(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((($true & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = true))) & ~ (~ (V_carte_1 = V_K0)
  & (V_lisible_1 = false))) & ~ (V_carte_1 = V_K0))
  & (V_lisible_1 = true)))).

tff(f68, type, f68: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f68_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f68(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((($true & mem($int, V_dte, V_DATE))
  & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true)))).

tff(f69, type, f69: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f69_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f69(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & $lesseq($sum(V_date_validite_1,1),V_dte)))).

tff(f71, type, f71: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f71_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f71(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & $lesseq($sum(V_date_validite_1,1),V_dte))
  & $lesseq(100,apply($int, $int, V_comptes, V_carte_1)))
  & $lesseq(V_dte,V_date_validite_1)))).

tff(f73, type, f73: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f73_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f73(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & $lesseq($sum(V_date_validite_1,1),V_dte))
  & (e_Perimee = e_Valide)))).

tff(f74, type, f74: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f74_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f74(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> $lesseq(100,apply($int,
  $int, V_comptes, V_carte_1)))).

tff(f76, type, f76: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f76_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f76(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & ~ $lesseq($sum(V_date_validite_1,1),V_dte))
  & $lesseq($sum(V_sld,1),100)))).

tff(f78, type, f78: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f78_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f78(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & ~ $lesseq($sum(V_date_validite_1,1),V_dte))
  & $lesseq($sum(V_sld,1),100)) & $lesseq(100,apply($int, $int, V_comptes,
  V_carte_1))) & $lesseq(V_dte,V_date_validite_1)))).

tff(f80, type, f80: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f80_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f80(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & ~ $lesseq($sum(V_date_validite_1,1),V_dte))
  & $lesseq($sum(V_sld,1),100)) & (e_Epuisee = e_Valide)))).

tff(f81, type, f81: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f81_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f81(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1))))
  & (V_ctrl = e_Valide)) & ~ $lesseq($sum(V_date_validite_1,1),V_dte)) & ~
  $lesseq($sum(V_sld,1),100)))).

tff(f83, type, f83: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f83_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f83(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1)))) & ~
  (V_ctrl = e_Valide)))).

tff(f84, type, f84: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f84_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f84(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((($true
  & mem($int, V_dte, V_DATE)) & ~ (V_carte_1 = V_K0)) & (V_lisible_1 = true))
  & $true) & mem(enum_STATUT, V_ctrl,
  union(enum_STATUT, union(enum_STATUT, singleton(enum_STATUT, e_Valide),
  singleton(enum_STATUT, e_Invalide)), singleton(enum_STATUT, e_Interdite))))
  & mem($int, V_sld, integer)) & $lesseq(0,V_sld))
  & $lesseq(V_sld,2147483647)) & ((mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)) => (V_ctrl = e_Valide)))
  & ((V_ctrl = e_Valide) => (mem($int, V_carte_1, V_clients) & ~
  mem($int, V_carte_1, V_interdits)))) & (mem($int, V_carte_1, V_interdits)
  => (V_ctrl = e_Interdite))) & ((V_ctrl = e_Interdite)
  => mem($int, V_carte_1, V_interdits))) & (~ mem($int, V_carte_1, V_clients)
  => (V_ctrl = e_Invalide))) & ((V_ctrl = e_Invalide) => ~
  mem($int, V_carte_1, V_clients))) & (mem($int, V_carte_1, V_clients)
  => (V_sld = apply($int, $int, V_comptes, V_carte_1)))) & ~
  (V_ctrl = e_Valide)) & mem($int, V_carte_1, V_clients)) & ~
  mem($int, V_carte_1, V_interdits)) & $lesseq(100,apply($int,
  $int, V_comptes, V_carte_1))) & $lesseq(V_dte,V_date_validite_1)))).

tff(f89, type, f89: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f89_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f89(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & ~ (V_carte_1 = V_K0)))).

tff(f90, type, f90: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f90_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f90(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & ~ (V_carte_1 = V_K0)))).

tff(f91, type, f91: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f91_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f91(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & (V_carte_1 = V_K0)))).

tff(f92, type, f92: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f92_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f92(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((($true & (V_carte_1 = V_K0))
  & $true) & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)))).

tff(f93, type, f93: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f93_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f93(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((($true & (V_carte_1 = V_K0))
  & $true) & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))))).

tff(f94, type, f94: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f94_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f94(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & (V_fin = false)))).

tff(f95, type, f95: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f95_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f95(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false)))
  & $lesseq(1,$difference(V_delai_0,1))))).

tff(f96, type, f96: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f96_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f96(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & $true) & $true) & $true)
  & mem($int, V_lectdelai_2, integer)) & $lesseq(0,V_lectdelai_2))
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = true)) & (V_ii_0 = false)))).

tff(f97, type, f97: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f97_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f97(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & $true) & $true) & $true)
  & mem($int, V_lectdelai_2, integer)) & $lesseq(0,V_lectdelai_2))
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = true)) & (V_ii_0 = false)) & $true) & $true))).

tff(f98, type, f98: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f98_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f98(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((((((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & $true) & $true) & $true)
  & mem($int, V_lectdelai_2, integer)) & $lesseq(0,V_lectdelai_2))
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = true)) & (V_ii_0 = false)) & $true) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_lectdelai_2)))
  & ($lesseq(2,V_lectdelai_2) => (V_fin_0 = false))))).

tff(f99, type, f99: (bool * bool * $int * bool * bool * bool * $int * $int *
  bool * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  set($int) * bool * bool * bool * bool * bool * $int * $int * $int * $int *
  $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * set($int)) > $o).

tff(f99_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int, V_pre_7777:
  bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:$int,
  V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f99(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & $true) & $true) & $true)
  & mem($int, V_lectdelai_2, integer)) & $lesseq(0,V_lectdelai_2))
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = true)) & (V_ii_0 = false)) & $true) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_lectdelai_2)))
  & ($lesseq(2,V_lectdelai_2) => (V_fin_0 = false))) & (V_fin_0 = false)))).

tff(f100, type, f100: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f100_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f100(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & $true) & $true) & $true)
  & mem($int, V_lectdelai_2, integer)) & $lesseq(0,V_lectdelai_2))
  & ((V_lectfin_delai_2 = false) => $lesseq(1,V_lectdelai_2)))
  & ($lesseq(1,V_lectdelai_2) => (V_lectfin_delai_2 = false)))
  & (V_fin_del_0 = V_lectfin_delai_2)) & (V_fin_del_0 = false))
  & (V_pre_0 = true)) & (V_ii_0 = false)) & $true) & $true) & $true)
  & ((V_fin_0 = false) => $lesseq(2,V_lectdelai_2)))
  & ($lesseq(2,V_lectdelai_2) => (V_fin_0 = false)))
  & $lesseq(1,$difference(V_lectdelai_2,1))))).

tff(f101, type, f101: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f101_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f101(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & $true) & $true)
  & mem($int, V_lectdelaiz_7778, integer)) & $lesseq(0,V_lectdelaiz_7778))
  & ((V_lectfin_delaiz_7778 = false) => $lesseq(1,V_lectdelaiz_7778)))
  & ($lesseq(1,V_lectdelaiz_7778) => (V_lectfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & mem($int, 0, integer)))).

tff(f102, type, f102: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f102_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f102(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & ~ ((V_ii_7777 = false)
  & (V_lectfin_delaiz_7778 = false))) & $true) & $true)
  & mem($int, V_lectdelaiz_7778, integer)) & $lesseq(0,V_lectdelaiz_7778))
  & ((V_lectfin_delaiz_7778 = false) => $lesseq(1,V_lectdelaiz_7778)))
  & ($lesseq(1,V_lectdelaiz_7778) => (V_lectfin_delaiz_7778 = false)))
  & mem($int, V_delai_0, integer)) & $lesseq(0,V_delai_0))
  & $lesseq(V_delai_0,2147483647)) & ~ (V_delai_0 = 0)) & $true)
  & ((V_fin = false) => $lesseq(2,V_delai_0))) & ($lesseq(2,V_delai_0)
  => (V_fin = false))) & ~ (V_ii_7777 = true)) & mem($int, 0, integer)))).

tff(f103, type, f103: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f103_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f103(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> (((((((((((((((((((($true
  & (V_carte_1 = V_K0)) & $true) & ~ (((V_pre_7777 = true)
  & (V_ii_7777 = false)) & (V_lectfin_delaiz_7778 = false))) & $true)
  & $true) & $true) & mem($int, V_lectdelaiz_7778, integer))
  & $lesseq(0,V_lectdelaiz_7778)) & ((V_lectfin_delaiz_7778 = false)
  => $lesseq(1,V_lectdelaiz_7778))) & ($lesseq(1,V_lectdelaiz_7778)
  => (V_lectfin_delaiz_7778 = false))) & mem($int, V_delai_0, integer))
  & $lesseq(0,V_delai_0)) & $lesseq(V_delai_0,2147483647)) & ~
  (V_delai_0 = 0)) & $true) & ((V_fin = false) => $lesseq(2,V_delai_0)))
  & ($lesseq(2,V_delai_0) => (V_fin = false))) & ~ (V_ii_7777 = true)) & ~
  (V_pre_7777 = true)) & mem($int, 0, integer)))).

tff(f104, type, f104: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f104_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f104(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((($true & $true)
  & (V_carte_1 = V_K0)) & (V_pre_1 = true)))).

tff(f106, type, f106: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f106_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f106(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ((($true & $true) & ~
  (V_pre_1 = true)) & (V_carte_1 = V_K0)))).

tff(f108, type, f108: (bool * bool * $int * bool * bool * bool * $int *
  $int * bool * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * set($int) * bool * bool * bool * bool * bool * $int * $int * $int *
  $int * $int * enum_STATUT * set(tuple2($int, $int)) * set($int) * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * $int *
  $int * $int * set($int) * set($int)) > $o).

tff(f108_def, axiom, ![V_val_0:bool, V_tst_lct_0:bool, V_sld:$int,
  V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:$int, V_lmt_0:
  $int, V_lisible_1:bool, V_lisible:bool, V_lectfin_delaiz_7778:bool,
  V_lectfin_delai_2:bool, V_lectfin_delai_1:bool, V_lectfin_delai:bool,
  V_lectdelaiz_7778:$int, V_lectdelai_2:$int, V_lectdelai_1:$int,
  V_lectdelai:$int, V_interdits:set($int), V_ii_7777:bool, V_ii_0:bool,
  V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int, V_delai_0:$int,
  V_date_validite_1:$int, V_date_validite:$int, V_date:$int, V_ctrl:
  enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: (f108(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) <=> ($true & ~ (V_carte_1 = V_K0)))).

tff(validation_infos_carte_11, conjecture, ![V_val_0:bool, V_tst_lct_0:bool,
  V_sld:$int, V_pre_7777:bool, V_pre_1:bool, V_pre_0:bool, V_nro_carte_0:
  $int, V_lmt_0:$int, V_lisible_1:bool, V_lisible:bool,
  V_lectfin_delaiz_7778:bool, V_lectfin_delai_2:bool, V_lectfin_delai_1:bool,
  V_lectfin_delai:bool, V_lectdelaiz_7778:$int, V_lectdelai_2:$int,
  V_lectdelai_1:$int, V_lectdelai:$int, V_interdits:set($int), V_ii_7777:
  bool, V_ii_0:bool, V_fin_del_0:bool, V_fin_0:bool, V_fin:bool, V_dte:$int,
  V_delai_0:$int, V_date_validite_1:$int, V_date_validite:$int, V_date:$int,
  V_ctrl:enum_STATUT, V_comptes:set(tuple2($int, $int)), V_clients:set($int),
  V_cde_carte_1:$int, V_cde_carte:$int, V_cdd_0:$int, V_carte_1:$int,
  V_carte:$int, V_b_verrous_1:bool, V_b_verrous:bool, V_b_carte_1:bool,
  V_b_carte:bool, V_K0:$int, V_HS:$int, V_D_min:$int, V_D_max:$int, V_DATE:
  set($int), V_CARTE:set($int)]: ((f1(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) & (f2(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) & (f10(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) & ($true & (f68(V_val_0, V_tst_lct_0,
  V_sld, V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) & (f81(V_val_0, V_tst_lct_0, V_sld,
  V_pre_7777, V_pre_1, V_pre_0, V_nro_carte_0, V_lmt_0, V_lisible_1,
  V_lisible, V_lectfin_delaiz_7778, V_lectfin_delai_2, V_lectfin_delai_1,
  V_lectfin_delai, V_lectdelaiz_7778, V_lectdelai_2, V_lectdelai_1,
  V_lectdelai, V_interdits, V_ii_7777, V_ii_0, V_fin_del_0, V_fin_0, V_fin,
  V_dte, V_delai_0, V_date_validite_1, V_date_validite, V_date, V_ctrl,
  V_comptes, V_clients, V_cde_carte_1, V_cde_carte, V_cdd_0, V_carte_1,
  V_carte, V_b_verrous_1, V_b_verrous, V_b_carte_1, V_b_carte, V_K0, V_HS,
  V_D_min, V_D_max, V_DATE, V_CARTE) & $true))))))
  => ($lesseq(V_dte,V_date_validite_1) & $true))).
