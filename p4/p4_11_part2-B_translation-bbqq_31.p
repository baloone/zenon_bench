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

tff(enum_aa, type, enum_aa: $tType).

tff(e_bb, type, e_bb: enum_aa).

tff(e_cc, type, e_cc: enum_aa).

tff(e_dd, type, e_dd: enum_aa).

tff(e_ee, type, e_ee: enum_aa).

tff(e_ff, type, e_ff: enum_aa).

tff(e_gg, type, e_gg: enum_aa).

tff(e_hh, type, e_hh: enum_aa).

tff(e_ii, type, e_ii: enum_aa).

tff(match_enum_aa, type, match_enum_aa: !>[A : $tType]: ((enum_aa * A * A *
  A * A * A * A * A * A) > A)).

tff(match_enum_aa_E_bb, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_bb, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z)).

tff(match_enum_aa_E_cc, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_cc, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z1)).

tff(match_enum_aa_E_dd, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_dd, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z2)).

tff(match_enum_aa_E_ee, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_ee, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z3)).

tff(match_enum_aa_E_ff, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_ff, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z4)).

tff(match_enum_aa_E_gg, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_gg, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z5)).

tff(match_enum_aa_E_hh, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_hh, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z6)).

tff(match_enum_aa_E_ii, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_ii, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z7)).

tff(e_bb_E_cc, axiom, ~ (e_bb = e_cc)).

tff(e_bb_E_dd, axiom, ~ (e_bb = e_dd)).

tff(e_bb_E_ee, axiom, ~ (e_bb = e_ee)).

tff(e_bb_E_ff, axiom, ~ (e_bb = e_ff)).

tff(e_bb_E_gg, axiom, ~ (e_bb = e_gg)).

tff(e_bb_E_hh, axiom, ~ (e_bb = e_hh)).

tff(e_bb_E_ii, axiom, ~ (e_bb = e_ii)).

tff(e_cc_E_dd, axiom, ~ (e_cc = e_dd)).

tff(e_cc_E_ee, axiom, ~ (e_cc = e_ee)).

tff(e_cc_E_ff, axiom, ~ (e_cc = e_ff)).

tff(e_cc_E_gg, axiom, ~ (e_cc = e_gg)).

tff(e_cc_E_hh, axiom, ~ (e_cc = e_hh)).

tff(e_cc_E_ii, axiom, ~ (e_cc = e_ii)).

tff(e_dd_E_ee, axiom, ~ (e_dd = e_ee)).

tff(e_dd_E_ff, axiom, ~ (e_dd = e_ff)).

tff(e_dd_E_gg, axiom, ~ (e_dd = e_gg)).

tff(e_dd_E_hh, axiom, ~ (e_dd = e_hh)).

tff(e_dd_E_ii, axiom, ~ (e_dd = e_ii)).

tff(e_ee_E_ff, axiom, ~ (e_ee = e_ff)).

tff(e_ee_E_gg, axiom, ~ (e_ee = e_gg)).

tff(e_ee_E_hh, axiom, ~ (e_ee = e_hh)).

tff(e_ee_E_ii, axiom, ~ (e_ee = e_ii)).

tff(e_ff_E_gg, axiom, ~ (e_ff = e_gg)).

tff(e_ff_E_hh, axiom, ~ (e_ff = e_hh)).

tff(e_ff_E_ii, axiom, ~ (e_ff = e_ii)).

tff(e_gg_E_hh, axiom, ~ (e_gg = e_hh)).

tff(e_gg_E_ii, axiom, ~ (e_gg = e_ii)).

tff(e_hh_E_ii, axiom, ~ (e_hh = e_ii)).

tff(enum_aa_inversion, axiom, ![U:enum_aa]: ((((((((U = e_bb) | (U = e_cc))
  | (U = e_dd)) | (U = e_ee)) | (U = e_ff)) | (U = e_gg)) | (U = e_hh))
  | (U = e_ii))).

tff(set_enum_aa, type, set_enum_aa: set(enum_aa)).

tff(set_enum_aa_axiom, axiom, ![X:enum_aa]: mem(enum_aa, X, set_enum_aa)).

tff(f1, type, f1: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f1_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f1(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((((((((((((((((((((($true & (V_bbll = 0))
  & (V_bbmm = 1)) & mem($int, V_bbnn, integer)) & $lesseq(0,V_bbnn))
  & $lesseq(V_bbnn,2147483647)) & mem($int, V_bboo, integer))
  & $lesseq(0,V_bboo)) & $lesseq(V_bboo,2147483647)) & mem($int, V_bbpp,
  integer)) & $lesseq(0,V_bbpp)) & $lesseq(V_bbpp,2147483647))
  & mem($int, V_yy, integer)) & $lesseq(0,V_yy)) & $lesseq(V_yy,2147483647))
  & $lesseq(1,V_yy)) & $lesseq(V_yy,254)) & (V_yy = V_bboo))
  & mem($int, V_xx, integer)) & $lesseq(0,V_xx)) & $lesseq(V_xx,2147483647))
  & $lesseq(1,V_xx)) & $lesseq(V_xx,254)) & (V_xx = V_bboo))
  & mem($int, V_ww, integer)) & $lesseq(0,V_ww)) & $lesseq(V_ww,2147483647))
  & $lesseq(1,V_ww)) & $lesseq($sum(V_ww,1),2147483647)) & (V_ww = V_bbpp))
  & mem($int, V_vv, integer)) & $lesseq(0,V_vv)) & $lesseq(V_vv,2147483647))
  & $lesseq(2,V_vv)) & (V_vv = V_bbnn)) & $lesseq($sum(V_vv,V_xx),253))
  & $lesseq($sum($sum(V_vv,V_yy),V_xx),251)) & mem($int, V_zz, integer))
  & $lesseq(0,V_zz)) & $lesseq(V_zz,2147483647)) & $lesseq(1,V_zz))
  & $lesseq($sum(V_zz,1),254)) & (V_zz = V_bbnn)) & $true) & $true))).

tff(f2, type, f2: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f2_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f2(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((((((((($true & $true) & $true) & $true)
  & $true) & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & $true)
  & mem($int, V_tt, integer)) & $lesseq(0,V_tt)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & $true) & mem($int, V_kk, integer)) & $lesseq(0,V_kk))
  & ((V_jj = e_cc) => (V_tt = $difference(V_uu,V_kk)))) & (V_bbbb = V_ll))
  & (V_bbcc = V_mm)) & (V_bbdd = V_nn)) & (V_bbee = V_oo)) & (V_bbff = V_uu))
  & (V_bbgg = V_jj)) & (V_bbhh = V_pp)) & (V_bbii = V_qq)) & (V_bbjj = V_rr))
  & (V_bbkk = V_ss)))).

tff(f3, type, f3: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f3_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f3(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((($true & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_cc)) & (V_jj = e_bb)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_cc = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_cc = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_cc = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_cc = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_cc = e_bb)))) => ~ ((((((((((((((mem($int, 0, integer) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & (V_tt = $difference($sum(V_uu,1),0))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_cc = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_cc = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_cc = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_cc = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_cc = e_bb))))
  => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & (V_tt = $difference($sum(V_uu,1),0))))) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ((e_cc = e_bb)
  | (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_cc = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_cc = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_cc = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_cc = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_cc = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_cc = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_cc = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_cc = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_cc = e_bb))))) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & (V_tt = $difference($sum(V_uu,1),0))))) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff)) & ((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ((V_ss = V_uu)
  & (e_cc = e_gg))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (e_cc = e_bb))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_cc = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_cc = e_bb)))) => ~ ((((((((((((((mem($int, 0, integer) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & (V_tt = $difference($sum(V_uu,1),0))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_cc = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_cc = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_cc = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1)))
  & (e_cc = e_gg)))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_cc = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_cc = e_ff)))))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_cc = e_bb))))
  => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & (V_tt = $difference($sum(V_uu,1),0))))) & (((((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_cc = e_bb)) => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true)
  & $true) & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & (V_tt = $difference($sum(V_uu,1),0))))) & ((((((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_cc = e_ee)) => ~ ((((((((((((((mem($int, 0,
  integer) & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp,
  integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & (V_tt = $difference($sum(V_uu,1),0)))))
  & ((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_cc = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp))
  & (V_ss = $sum(V_uu,1))) => ~ ((((((((((((((mem($int, 0, integer) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & (V_tt = $difference($sum(V_uu,1),0)))))
  & ((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_cc = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp))
  & (V_ss = V_uu)) => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true)
  & $true) & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & (V_tt = $difference($sum(V_uu,1),0))))) & (((((((((((~ (V_jj = e_ii) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_dd)) & ~ (V_jj = e_cc)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) => ~ ((((((((((((((mem($int, 0,
  integer) & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp,
  integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ($sum(V_uu,1) = $difference($sum(V_uu,1),0))))))).

tff(f7, type, f7: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f7_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f7(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($true & $true))).

tff(f9, type, f9: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f9_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f9(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $difference($sum(V_uu,1),0), integer))).

tff(f10, type, f10: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f10_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f10(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(0,$difference($sum(V_uu,1),0)))).

tff(f11, type, f11: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f11_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f11(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((($true & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_cc)) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (V_jj = e_bb)) & ((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_ii)) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),0)))))) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ($lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) | (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (V_jj = e_bb))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_jj = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (V_jj = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (V_jj = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (V_jj = e_bb)))) => ~ ((((((((((((((mem($int, 0, integer) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),0)))))) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv) | (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (V_jj = e_ii)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (V_jj = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (V_jj = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (V_jj = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))
  => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((V_jj = e_cc) => (V_tt = $difference($sum(V_uu,1),0)))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & ((V_jj = e_bb) | (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((V_jj = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((V_jj = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((V_jj = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),0)))))) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ((V_ss = V_uu)
  & (V_jj = e_gg))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (V_jj = e_bb))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (V_jj = e_bb))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_rr = $sum(V_uu,1)))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb)))) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),0)))))) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (((V_rr = V_qq)
  & (V_ss = V_uu)) & (V_jj = e_gg))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (V_jj = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (V_jj = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1)))
  & (V_jj = e_gg)))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (V_jj = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (V_jj = e_ff)))))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))
  => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((V_jj = e_cc) => (V_tt = $difference($sum(V_uu,1),0))))))
  & (((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (V_jj = e_bb)) => ~ ((((((((((((((mem($int, 0,
  integer) & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp,
  integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),0)))))) & ((((((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (V_jj = e_ee)) => ~ ((((((((((((((mem($int, 0,
  integer) & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp,
  integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),0)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (V_jj = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((V_jj = e_cc) => (V_tt = $difference($sum(V_uu,1),0))))))
  & ((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (V_jj = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp))
  & (V_ss = V_uu)) => ~ ((((((((((((((mem($int, 0, integer) & $true) & $true)
  & $true) & $true) & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((V_jj = e_cc) => (V_tt = $difference($sum(V_uu,1),0)))))) & ((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_cc)) & (~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & ~ ![V_bbaa1:$int]:
  ((mem($int, V_bbaa1, integer) & $lesseq(0,V_bbaa1)) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_bbaa1 = $difference($sum(V_uu,1),0))))))))) => ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ![V_bbaa1:$int]:
  ((mem($int, V_bbaa1, integer) & $lesseq(0,V_bbaa1)) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_bbaa1 = $difference($sum(V_uu,1),0))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ![V_bbaa1:$int]:
  ((mem($int, V_bbaa1, integer) & $lesseq(0,V_bbaa1)) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_bbaa1 = $difference($sum(V_uu,1),0))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (V_jj = e_cc)) => ~
  ((((((((((((((mem($int, 0, integer) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => ($sum(V_uu,1) = $difference($sum(V_uu,1),0)))))))).

tff(f16, type, f16: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f16_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f16(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ?[V_bbaa1:$int]: ((mem($int, V_bbaa1, integer) & $lesseq(0,V_bbaa1))
  & ((V_jj = e_cc) => (V_bbaa1 = $difference($sum(V_uu,1),0)))))).

tff(f17, type, f17: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f17_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f17(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))))).

tff(f19, type, f19: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f19_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f19(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_kk,1), integer))).

tff(f20, type, f20: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f20_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f20(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(0,$sum(V_kk,1)))).

tff(f21, type, f21: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f21_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f21(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (e_bb = e_cc)))).

tff(f22, type, f22: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f22_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f22(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))).

tff(f23, type, f23: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f23_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f23(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & $lesseq(V_zz,$sum(V_kk,1))) & (V_jj = e_cc))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh))
  & (V_jj = e_ii)) & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_dd = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_dd = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_dd = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_dd = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_dd = e_bb)))) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_dd = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_dd = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_dd = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_dd = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & ((e_dd = e_bb) | (((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_dd = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_dd = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_dd = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb)))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & (V_jj = e_ff)) & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ((V_ss = V_uu) & (e_dd = e_gg))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (e_dd = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_dd = e_bb))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & (V_jj = e_ee)) & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_dd = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_dd = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_dd = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1)))
  & (e_dd = e_gg)))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_dd = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_dd = e_ff)))))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_dd = e_bb)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_dd = e_ee)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_dd = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & (((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_dd = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp))
  & (V_ss = V_uu)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_dd = e_bb)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (e_dd = e_bb))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & $lesseq(V_zz,$difference($sum(V_uu,1),V_tt))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))))).

tff(f27, type, f27: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f27_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f27(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($sum(V_uu,1) = V_pp))).

tff(f29, type, f29: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f29_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f29(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_uu,1), integer))).

tff(f30, type, f30: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f30_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f30(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(0,$sum(V_uu,1)))).

tff(f31, type, f31: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f31_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f31(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & $lesseq(V_zz,$sum(V_kk,1))) & (V_jj = e_cc))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh))
  & (V_jj = e_ii)) & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_dd = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_dd = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_dd = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_dd = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_dd = e_bb)))) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_dd = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_dd = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_dd = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_dd = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & ((e_dd = e_bb) | (((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_dd = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_dd = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_dd = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_dd = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb)))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & (V_jj = e_ff)) & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ((V_ss = V_uu) & (e_dd = e_gg))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (e_dd = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_dd = e_bb))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & (V_jj = e_ee)) & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_dd = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_dd = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_dd = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1)))
  & (e_dd = e_gg)))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_dd = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_dd = e_ff)))))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_dd = e_bb)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_dd = e_ee)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_dd = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & (((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_dd = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp))
  & (V_ss = V_uu)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_dd = e_bb))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_dd = e_bb)) & ($sum(V_uu,1) = V_pp)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (e_dd = e_bb))
  & ($sum(V_uu,1) = V_pp)) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_dd = e_cc) => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1)))))))
  & ((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & $lesseq(V_zz,$difference($sum(V_uu,1),V_tt))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_dd = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (e_dd = e_cc)))).

tff(f32, type, f32: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f32_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f32(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & ~ $lesseq(V_zz,$sum(V_kk,1))) & (V_jj = e_cc))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_ii)) => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & ($lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) | (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (V_jj = e_bb))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_jj = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (V_jj = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (V_jj = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (V_jj = e_bb)))) => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv) | (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (V_jj = e_ii)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (V_jj = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (V_jj = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (V_jj = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & ((V_jj = e_bb) | (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((V_jj = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((V_jj = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((V_jj = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (V_jj = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ((V_ss = V_uu) & (V_jj = e_gg))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (V_jj = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (V_jj = e_bb))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (V_rr = $sum(V_uu,1)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (V_jj = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (V_jj = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (V_jj = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1)))
  & (V_jj = e_gg)))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (V_jj = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (V_jj = e_ff)))))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (V_jj = e_bb)) => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (V_jj = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (V_jj = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (V_jj = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (V_jj = e_bb)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (V_jj = e_bb)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (V_jj = e_bb)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((V_jj = e_dd)
  & (V_pp = $sum(V_uu,1)))) | ~
  $lesseq(V_zz,$difference($sum(V_uu,1),V_tt)))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))))).

tff(f34, type, f34: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f34_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f34(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))))).

tff(f35, type, f35: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f35_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f35(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (e_bb = e_cc)))).

tff(f36, type, f36: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f36_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f36(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))))).

tff(f37, type, f37: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f37_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f37(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (e_bb = e_cc)))).

tff(f38, type, f38: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f38_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f38(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (V_jj = e_cc)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))))).

tff(f39, type, f39: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f39_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f39(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (V_jj = e_cc)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, $sum(V_kk,1), integer)
  & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, $sum(V_kk,1), integer) & $lesseq(0,$sum(V_kk,1)))
  & $true) & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, $sum(V_kk,1),
  integer) & $lesseq(0,$sum(V_kk,1))) & $true) & $true) & $true) & $true)
  & $true) & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq,
  integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),$sum(V_kk,1))))))) & (e_bb = e_cc)))).

tff(f40, type, f40: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f40_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f40(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_gg = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)))) & (V_uu = V_ss)) & (V_pp = V_rr)) & (V_pp = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (~ $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_gg = e_ii))) & (V_uu = V_ss)) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss)))) & (V_pp = V_qq)) & (V_pp = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & (((e_gg = e_bb)
  & (V_uu = V_ss)) | ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)))) & (V_uu = V_ss)) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss))))) & (V_pp = V_rr)) & (V_pp = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb)) & (V_uu = V_ss))) | ((((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) & (V_uu = V_ss)))
  & (V_pp = V_rr)) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & ((V_pp = V_rr)
  & (V_uu = V_ss))))) & (V_pp = V_qq)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (V_pp = V_qq)) & (V_pp = V_qq)) | ((((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_gg = e_bb)) & (V_pp = V_qq)))) & ((V_pp = V_rr) & (V_uu = V_ss))))
  | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) & (V_pp = V_rr)) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ff))) & (V_pp = V_qq))))
  & (V_uu = V_ss))) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & (((V_pp = V_rr)
  & (V_pp = V_qq)) & (V_uu = V_ss))))) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & (V_pp = V_qq)) & (V_uu = V_ss)) & (V_pp = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_pp = $sum(V_uu,1))) & (e_gg = e_ee)) & (V_pp = V_rr)) & (V_uu = V_ss))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_gg = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(f42, type, f42: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f42_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f42(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ~ (V_jj = e_dd))).

tff(f50, type, f50: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f50_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f50(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_gg = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)))) & (V_uu = V_ss)) & (V_pp = V_rr)) & (V_pp = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (~ $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_gg = e_ii))) & (V_uu = V_ss)) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss)))) & (V_pp = V_qq)) & (V_pp = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & (((e_gg = e_bb)
  & (V_uu = V_ss)) | ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)))) & (V_uu = V_ss)) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss))))) & (V_pp = V_rr)) & (V_pp = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb)) & (V_uu = V_ss))) | ((((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) & (V_uu = V_ss)))
  & (V_pp = V_rr)) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & ((V_pp = V_rr)
  & (V_uu = V_ss))))) & (V_pp = V_qq)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (V_pp = V_qq)) & (V_pp = V_qq)) | ((((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_gg = e_bb)) & (V_pp = V_qq)))) & ((V_pp = V_rr) & (V_uu = V_ss))))
  | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) & (V_pp = V_rr)) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ff))) & (V_pp = V_qq))))
  & (V_uu = V_ss))) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & (((V_pp = V_rr)
  & (V_pp = V_qq)) & (V_uu = V_ss))))) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & (V_pp = V_qq)) & (V_uu = V_ss)) & (V_pp = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_pp = $sum(V_uu,1))) & (e_gg = e_ee)) & (V_pp = V_rr)) & (V_uu = V_ss))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & (V_uu = V_ss)) & (V_pp = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_gg = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (e_gg = e_cc)))).

tff(f51, type, f51: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f51_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f51(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (V_tt = $difference($sum(V_uu,1),V_kk)))).

tff(f52, type, f52: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f52_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f52(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, $sum(V_pp,1), integer))
  & $lesseq(0,$sum(V_pp,1))) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((V_jj = e_cc)
  => ($sum(V_tt,1) = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((V_jj = e_dd)
  & (V_pp = V_uu)))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, $sum(V_pp,1), integer)) & $lesseq(0,$sum(V_pp,1)))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((V_jj = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(f53, type, f53: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f53_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f53(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($sum(V_pp,1) = V_pp))).

tff(f54, type, f54: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f54_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f54(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_pp,1), integer))).

tff(f55, type, f55: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f55_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f55(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(0,$sum(V_pp,1)))).

tff(f56, type, f56: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f56_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f56(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_gg = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)))) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_rr))
  & (V_pp = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii))
  & (V_jj = e_hh)) & ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_gg = e_ii))) & ($sum(V_uu,1) = V_ss)) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss)))) & (V_pp = V_qq))
  & (V_pp = V_rr)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & (((e_gg = e_bb) & ($sum(V_uu,1) = V_ss))
  | ((((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)))) & ($sum(V_uu,1) = V_ss)) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx) | ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx) | ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx) | ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))))) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & ($sum(V_uu,1) = V_ss))))) & (V_pp = V_rr)) & (V_pp = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & (((((((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))) & (V_pp = V_rr)) | (((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & ((V_pp = V_rr) & ($sum(V_uu,1) = V_ss)))))
  & (V_pp = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & (V_jj = e_ee)) & (((((((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_gg = e_bb)) & (V_pp = V_qq)))) & ((V_pp = V_rr)
  & ($sum(V_uu,1) = V_ss))) | ((((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (V_pp = V_qq)) & (V_pp = V_qq)))
  | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) & (V_pp = V_rr)) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ff))) & (V_pp = V_qq))))
  & ($sum(V_uu,1) = V_ss))) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & (((V_pp = V_rr)
  & (V_pp = V_qq)) & ($sum(V_uu,1) = V_ss))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & (V_pp = V_qq)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_rr))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_pp = $sum(V_uu,1))) & (e_gg = e_ee)) & (V_pp = V_rr))
  & ($sum(V_uu,1) = V_ss)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_pp = V_rr)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_pp = V_rr)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_pp = V_rr)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_gg = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(f57, type, f57: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f57_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f57(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($sum(V_uu,1) = V_ss))).

tff(f59, type, f59: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f59_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f59(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_gg = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)))) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_rr))
  & (V_pp = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii))
  & (V_jj = e_hh)) & ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_gg = e_ii))) & ($sum(V_uu,1) = V_ss)) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss)))) & (V_pp = V_qq))
  & (V_pp = V_rr)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & (((e_gg = e_bb) & ($sum(V_uu,1) = V_ss))
  | ((((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)))) & ($sum(V_uu,1) = V_ss)) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx) | ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx) | ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx) | ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))))) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & ($sum(V_uu,1) = V_ss))))) & (V_pp = V_rr)) & (V_pp = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & (((((((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_gg = e_bb)) & ($sum(V_uu,1) = V_ss))) & (V_pp = V_rr)) | (((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & ((V_pp = V_rr) & ($sum(V_uu,1) = V_ss)))))
  & (V_pp = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & (V_jj = e_ee)) & (((((((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_gg = e_bb)) & (V_pp = V_qq)))) & ((V_pp = V_rr)
  & ($sum(V_uu,1) = V_ss))) | ((((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (V_pp = V_qq)) & (V_pp = V_qq)))
  | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ee))) & (V_pp = V_rr)) | ((~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_pp = $sum(V_uu,1)) & (e_gg = e_ff))) & (V_pp = V_qq))))
  & ($sum(V_uu,1) = V_ss))) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & (((V_pp = V_rr)
  & (V_pp = V_qq)) & ($sum(V_uu,1) = V_ss))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & (V_pp = V_qq)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_rr))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_pp = $sum(V_uu,1))) & (e_gg = e_ee)) & (V_pp = V_rr))
  & ($sum(V_uu,1) = V_ss)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_pp = V_rr)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_pp = V_rr)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & (V_pp = V_rr)) & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_pp = V_rr))
  & ($sum(V_uu,1) = V_ss)) & (V_pp = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_gg = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_pp, integer)) & $lesseq(0,V_pp))
  & mem($int, $sum(V_uu,1), integer)) & $lesseq(0,$sum(V_uu,1)))
  & ((e_gg = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (e_gg = e_cc)))).

tff(f60, type, f60: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f60_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f60(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_ee = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_ee = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_ee = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)))) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_ee = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & ((e_ee = e_bb) | (((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb)))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & (V_jj = e_ff)) & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ((V_ss = V_uu) & (e_ee = e_gg))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (e_ee = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_ee = e_bb))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & (V_jj = e_ee)) & ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu))
  & (e_ee = e_gg))) & ($sum(V_uu,1) = V_qq)) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  | ((~ $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq))))) | ((((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (((V_rr = V_qq)
  & (V_ss = $sum(V_uu,1))) & (e_ee = e_gg))) & ($sum(V_uu,1) = V_qq)))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  | ((~ $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_ee = e_ff))) & ($sum(V_uu,1) = V_qq)))))
  | (((((~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq)))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_ee = e_gg)) & ($sum(V_uu,1) = V_pp)) & (V_rr = V_pp))
  & (V_ss = $sum(V_uu,1))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_gg)) & ($sum(V_uu,1) = V_pp))
  & (V_rr = V_pp)) & (V_ss = V_uu)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ($sum(V_uu,1) = V_qq))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_ee = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_ee = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(f61, type, f61: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f61_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f61(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($sum(V_uu,1) = V_qq))).

tff(f64, type, f64: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f64_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f64(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_ee = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_ee = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_ee = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)))) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_ee = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & ((e_ee = e_bb) | (((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb)))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & (V_jj = e_ff)) & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ((V_ss = V_uu) & (e_ee = e_gg))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (e_ee = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_ee = e_bb))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & (V_jj = e_ee)) & ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu))
  & (e_ee = e_gg))) & ($sum(V_uu,1) = V_qq)) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  | ((~ $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq))))) | ((((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (((V_rr = V_qq)
  & (V_ss = $sum(V_uu,1))) & (e_ee = e_gg))) & ($sum(V_uu,1) = V_qq)))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  | ((~ $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_ee = e_ff))) & ($sum(V_uu,1) = V_qq)))))
  | (((((~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq)))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_ee = e_gg)) & ($sum(V_uu,1) = V_pp)) & (V_rr = V_pp))
  & (V_ss = $sum(V_uu,1))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_gg)) & ($sum(V_uu,1) = V_pp))
  & (V_rr = V_pp)) & (V_ss = V_uu)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ($sum(V_uu,1) = V_qq))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_ee = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_ee = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (e_ee = e_cc)))).

tff(f65, type, f65: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f65_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f65(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ee)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (V_jj = e_dd)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_ii)
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_ii)
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_ii)
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(f66, type, f66: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f66_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f66(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ee)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (V_jj = e_dd)) & (((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) | ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) | (((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_bb = e_ii))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_bb = e_gg)))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = V_uu) & (e_bb = e_gg))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) | ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_bb = e_gg)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | ~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (((V_rr = V_qq) & (V_ss = $sum(V_uu,1))) & (e_bb = e_gg))))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_bb = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_bb = e_ff)))))) | (((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_bb = e_ee)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = $sum(V_uu,1)))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_bb = e_gg)) & (V_qq = V_pp)) & (V_rr = V_pp)) & (V_ss = V_uu)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & mem($int, V_ss, integer))
  & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_ii)
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_ii)
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((~ (V_jj = e_ii)
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_ll = true))
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_bb = e_dd)
  & (V_pp = $sum(V_uu,1))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_bb = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (e_bb = e_cc)))).

tff(f67, type, f67: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f67_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f67(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & (V_jj = e_ee)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_gg = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)))) & (V_uu = V_ss)) & (V_qq = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (~ $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_gg = e_ii))) & (V_uu = V_ss)) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss)))) & (V_qq = V_rr)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & (((e_gg = e_bb)
  & (V_uu = V_ss)) | ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)))) & (V_uu = V_ss)) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss))))) & (V_qq = V_rr)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb)) & (V_uu = V_ss))) | ((((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) & (V_uu = V_ss)))
  & (V_qq = V_rr)) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & ((V_qq = V_rr)
  & (V_uu = V_ss))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_gg = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_gg = e_bb)))) & ((V_qq = V_rr) & (V_uu = V_ss))))
  | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_gg = e_ee))) & (V_qq = V_rr)) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_gg = e_ff))))) & (V_uu = V_ss))) | (((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & ((V_qq = V_rr) & (V_uu = V_ss))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & (V_uu = V_ss)) & (V_qq = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_gg = e_ee)) & (V_qq = V_rr)) & (V_uu = V_ss))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (V_qq = V_pp)) & (V_qq = V_pp)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & (V_ll = false)) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt))
  & ((e_gg = e_dd) & (V_pp = $sum(V_uu,1))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(f68, type, f68: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f68_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f68(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ~ (V_jj = e_ee))).

tff(f70, type, f70: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f70_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f70(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ff)) & (V_jj = e_ee)) & (V_ll = false)) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (((((((((((~ (V_jj = e_bb) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (((((((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_gg = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_gg = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)))) & (V_uu = V_ss)) & (V_qq = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (~ $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_gg = e_ii))) & (V_uu = V_ss)) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss)))) & (V_qq = V_rr)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & (((e_gg = e_bb)
  & (V_uu = V_ss)) | ((((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)))) & (V_uu = V_ss)) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & ((~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_gg = e_bb)) & (V_uu = V_ss)))) | (((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb))
  & (V_uu = V_ss))))) & (V_qq = V_rr)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & (V_jj = e_ff))
  & ((((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_gg = e_bb)) & (V_uu = V_ss))) | ((((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & (e_gg = e_bb)) & (V_uu = V_ss)))
  & (V_qq = V_rr)) | (((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_gg = e_bb)) & ((V_qq = V_rr)
  & (V_uu = V_ss))))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & (((((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  | ((((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_gg = e_ee))) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_gg = e_bb)))) & ((V_qq = V_rr) & (V_uu = V_ss))))
  | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_gg = e_ee))) & (V_qq = V_rr)) | (~
  $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_qq = $sum(V_uu,1)) & (e_gg = e_ff))))) & (V_uu = V_ss))) | (((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & ((V_qq = V_rr) & (V_uu = V_ss))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_gg = e_bb)) & (V_uu = V_ss)) & (V_qq = V_rr)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (V_qq = $sum(V_uu,1))) & (e_gg = e_ee)) & (V_qq = V_rr)) & (V_uu = V_ss))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (V_qq = V_pp)) & (V_qq = V_pp)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & (V_ll = false)) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_gg = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, V_qq, integer))
  & $lesseq(0,V_qq)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & (V_qq = V_rr))
  & (V_uu = V_ss)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ($lesseq(V_zz,$difference($sum(V_uu,1),V_tt))
  & ((e_gg = e_dd) & (V_pp = $sum(V_uu,1))))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, V_qq, integer)) & $lesseq(0,V_qq))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & mem($int, V_uu, integer))
  & $lesseq(0,V_uu)) & ((e_gg = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (e_gg = e_cc)))).

tff(f71, type, f71: ($int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * bool * bool * bool * bool * $int * enum_aa * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * enum_aa * $int *
  bool * bool * bool * bool * $int) > $o).

tff(f71_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa, V_bbpp:
  $int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:$int,
  V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int, V_bbee:
  bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]: (f71(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ff))
  & $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy))
  & (V_jj = e_ee)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_ii)) & (e_ee = V_jj)) & ($sum(V_uu,1) = V_qq))
  => ~ (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww))
  & (e_ee = V_jj)) | (~
  $lesseq($sum($difference(V_uu,V_ss),1),$sum(V_vv,V_ww)) & (e_ee = e_bb))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_ee = e_bb))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_bb))) | (((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false)) & (e_ee = e_bb))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)))) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_ee = V_jj)) | (~
  $lesseq($sum($difference($difference($sum(V_uu,1),V_ss),1),1),V_vv)
  & (e_ee = e_ii)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg))))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg)))) | (((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ((V_ss = $sum(V_uu,1)) & (e_ee = e_gg)))) | ((((~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & (V_jj = e_gg)) & ((e_ee = e_bb) | (((((((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_hh)) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb)))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | (((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | (((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))
  & (($lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & ((e_ee = e_gg) & (V_ss = $sum(V_uu,1)))) | (~
  $lesseq($difference($difference($sum(V_uu,1),V_rr),1),V_xx)
  & (e_ee = e_bb))))) | ((((~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb)))))
  & ($sum(V_uu,1) = V_qq)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg))
  & (V_jj = e_ff)) & (((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ((V_ss = V_uu) & (e_ee = e_gg))) | (((((V_ll = true)
  & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) & (e_ee = e_bb)))
  | (((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_ee = e_bb))) | ((((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false)) & (V_rr = $sum(V_uu,1))) & (e_ee = V_jj))) | ((((~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)))) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((~ (V_jj = e_bb)
  & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh))
  & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & (V_jj = e_ee))
  & ((((((((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (((V_rr = V_qq) & (V_ss = V_uu)) & (e_ee = e_gg)))
  & ($sum(V_uu,1) = V_qq)) | (((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  | ((~ $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq))))) | ((((((V_ll = true)
  & (V_mm = true)) & (V_nn = true)) & (V_oo = false)) & (((V_rr = V_qq)
  & (V_ss = $sum(V_uu,1))) & (e_ee = e_gg))) & ($sum(V_uu,1) = V_qq)))
  | (((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & ($lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  | ((~ $lesseq($sum($difference($difference($sum(V_qq,1),V_pp),1),1),V_yy)
  & ((V_rr = $sum(V_uu,1)) & (e_ee = e_ff))) & ($sum(V_uu,1) = V_qq)))))
  | (((((~ ((((V_ll = false) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true)) & (V_nn = false))
  & (V_oo = false))) & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq)))) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd)) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))) & ~
  ((((V_ll = true) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))) & ~
  ((((V_ll = false) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)))
  & (e_ee = e_bb)) & ($sum(V_uu,1) = V_qq)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & ((((((((((((((((~
  (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & (V_jj = e_dd))
  & (V_ll = true)) & (V_mm = true)) & (V_nn = true)) & (V_oo = false))
  & (e_ee = e_gg)) & ($sum(V_uu,1) = V_pp)) & (V_rr = V_pp))
  & (V_ss = $sum(V_uu,1))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & ((((((((((((((((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~ (V_jj = e_ii)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee))
  & (V_jj = e_dd)) & (V_ll = false)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_gg)) & ($sum(V_uu,1) = V_pp))
  & (V_rr = V_pp)) & (V_ss = V_uu)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & ~ ((((V_ll = true) & (V_mm = true))
  & (V_nn = true)) & (V_oo = false))) & ~ ((((V_ll = false) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))) & (e_ee = e_bb)) => ~
  (((((((((((((((mem($int, V_kk, integer) & $lesseq(0,V_kk)) & $true)
  & $true) & $true) & $true) & $true) & mem($int, V_pp, integer))
  & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1), integer))
  & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer)) & $lesseq(0,V_rr))
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & ((e_ee = e_cc)
  => (V_tt = $difference($sum(V_uu,1),V_kk)))))) & (((((((((((((~
  (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc)) & ($sum(V_uu,1) = V_qq))
  & (V_ll = false)) & (V_mm = true)) & (V_nn = false)) & (V_oo = false))
  & (e_ee = e_bb)) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & (V_ll = true)) & (V_mm = true)) & (V_nn = true))
  & (V_oo = false)) & (e_ee = e_bb)) => ~ (((((((((((((((mem($int, V_kk,
  integer) & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk))))))
  & (((((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & (V_jj = e_cc))
  & ($sum(V_uu,1) = V_qq)) & (V_ll = true)) & (V_mm = true))
  & (V_nn = false)) & (V_oo = false))
  & (($lesseq(V_zz,$difference($sum(V_uu,1),V_tt)) & ((e_ee = e_dd)
  & (V_pp = $sum(V_uu,1)))) | (~ $lesseq(V_zz,$difference($sum(V_uu,1),V_tt))
  & (e_ee = V_jj)))) => ~ (((((((((((((((mem($int, V_kk, integer)
  & $lesseq(0,V_kk)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & mem($int, $sum(V_uu,1),
  integer)) & $lesseq(0,$sum(V_uu,1))) & mem($int, V_rr, integer))
  & $lesseq(0,V_rr)) & mem($int, V_ss, integer)) & $lesseq(0,V_ss))
  & ((e_ee = e_cc) => (V_tt = $difference($sum(V_uu,1),V_kk)))))))).

tff(bbqq_31, conjecture, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:
  $int, V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int,
  V_oo:bool, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:$int, V_jj:enum_aa,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:enum_aa, V_bbff:$int,
  V_bbee:bool, V_bbdd:bool, V_bbcc:bool, V_bbbb:bool, V_bbaa:$int]:
  ((f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) & (f2(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr,
  V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn,
  V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee,
  V_bbdd, V_bbcc, V_bbbb, V_bbaa) & ($true & (f34(V_zz, V_yy, V_xx, V_ww,
  V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk,
  V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & $true))))
  => (f20(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) & $true))).
