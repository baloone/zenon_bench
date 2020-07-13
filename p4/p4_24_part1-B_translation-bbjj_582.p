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

tff(f1, type, f1: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f1_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((((((((((((((((((((($true & (V_bbdd = 0))
  & (V_bbee = 1)) & mem($int, V_bbff, integer)) & $lesseq(0,V_bbff))
  & $lesseq(V_bbff,2147483647)) & mem($int, V_bbgg, integer))
  & $lesseq(0,V_bbgg)) & $lesseq(V_bbgg,2147483647)) & mem($int, V_bbhh,
  integer)) & $lesseq(0,V_bbhh)) & $lesseq(V_bbhh,2147483647))
  & mem($int, V_ww, integer)) & $lesseq(0,V_ww)) & $lesseq(V_ww,2147483647))
  & $lesseq(1,V_ww)) & $lesseq(V_ww,254)) & (V_ww = V_bbgg))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & $lesseq(V_uu,2147483647))
  & $lesseq(1,V_uu)) & $lesseq(V_uu,254)) & (V_uu = V_bbgg))
  & mem($int, V_rr, integer)) & $lesseq(0,V_rr)) & $lesseq(V_rr,2147483647))
  & $lesseq(1,V_rr)) & $lesseq($sum(V_rr,1),2147483647)) & (V_rr = V_bbhh))
  & mem($int, V_qq, integer)) & $lesseq(0,V_qq)) & $lesseq(V_qq,2147483647))
  & $lesseq(2,V_qq)) & (V_qq = V_bbff)) & $lesseq($sum(V_qq,V_uu),253))
  & $lesseq($sum($sum(V_qq,V_ww),V_uu),251)) & mem($int, V_yy, integer))
  & $lesseq(0,V_yy)) & $lesseq(V_yy,2147483647)) & $lesseq(1,V_yy))
  & $lesseq($sum(V_yy,1),254)) & (V_yy = V_bbff)) & $true) & $true))).

tff(f16, type, f16: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f16_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f16(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((($true & mem($int, V_xx, mk(0, 255)))
  & mem($int, V_vv, mk(0, 255))) & mem($int, V_tt, mk(0, 255)))
  & mem($int, V_ss, mk(0, 255))) & mem($int, V_oo, integer))
  & $lesseq(0,V_oo)) & $true) & $true) & $true) & $true) & $true)
  & mem($int, V_pp, integer)) & $lesseq(0,V_pp)) & (mem(enum_aa, V_jj,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))
  => (V_vv = 0))) & ((V_jj = e_cc) => $lesseq(V_xx,V_yy))) & ((V_jj = e_ee)
  => $lesseq(V_vv,V_ww))) & ((V_jj = e_ff) => $lesseq(V_vv,$sum(V_ww,1))))
  & (mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff))) => (V_tt = 0))) & (mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff))) => (V_ss = 0))) & ((V_jj = e_gg)
  => $lesseq(V_ss,1))) & ((V_jj = e_gg) => ($difference(V_oo,V_pp) = V_ss)))
  & (mem(enum_aa, V_jj, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh))) => ($lesseq(V_tt,$sum($sum(V_qq,V_uu),1))
  & $lesseq(V_vv,$sum($sum(V_ww,V_tt),2))))) & ((V_jj = e_hh)
  => ((($difference($difference(V_oo,1),V_pp) = V_ss)
  & $lesseq(V_tt,$sum(V_ss,V_uu))) & $lesseq(V_ss,V_qq)))))).

tff(f20, type, f20: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f20_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f20(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_oo,1),
  integer))).

tff(f21, type, f21: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f21_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f21(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(0,$sum(V_oo,1)))).

tff(f46, type, f46: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f46_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f46(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_vv,$sum(V_ww,1)))).

tff(f55, type, f55: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f55_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f55(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference($sum(V_oo,1),V_pp) = V_ss))).

tff(f57, type, f57: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f57_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f57(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_tt,$sum($sum(V_qq,V_uu),1)))).

tff(f58, type, f58: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f58_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f58(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_vv,$sum($sum(V_ww,V_tt),2)))).

tff(f60, type, f60: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f60_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f60(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference($difference($sum(V_oo,1),1),V_pp) = V_ss))).

tff(f61, type, f61: (bool * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f61_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f61(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_tt,$sum(V_ss,V_uu)))).

tff(f146, type, f146: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f146_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f146(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_vv,1),
  mk(0, 255)))).

tff(f148, type, f148: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f148_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f148(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ($sum(V_vv,1) = 0))).

tff(f151, type, f151: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f151_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f151(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_vv,1),V_ww))).

tff(f235, type, f235: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f235_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f235(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_tt,1),
  mk(0, 255)))).

tff(f241, type, f241: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f241_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f241(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ($sum(V_tt,1) = 0))).

tff(f244, type, f244: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f244_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f244(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_tt,$sum(V_qq,V_uu)))).

tff(f245, type, f245: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f245_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f245(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_vv,1),$sum($sum(V_ww,$sum(V_tt,1)),2)))).

tff(f247, type, f247: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f247_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f247(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_tt,1),$sum(V_ss,V_uu)))).

tff(f271, type, f271: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f271_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f271(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference($sum(V_oo,1),$sum(V_oo,1)) = 0))).

tff(f274, type, f274: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f274_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f274(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference($difference($sum(V_oo,1),1),$sum(V_oo,1)) = 0))).

tff(f275, type, f275: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f275_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f275(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_tt,1),$sum(0,V_uu)))).

tff(f312, type, f312: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f312_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f312(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & (e_bb = e_cc)))).

tff(f313, type, f313: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f313_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f313(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & (e_bb = e_ee)))).

tff(f314, type, f314: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f314_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f314(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & (e_bb = e_ff)))).

tff(f315, type, f315: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f315_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f315(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f316, type, f316: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f316_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f316(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & (e_bb = e_gg)))).

tff(f317, type, f317: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f317_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f317(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f318, type, f318: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f318_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f318(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)) & ~
  $lesseq($sum(V_tt,1),V_uu)) & (e_bb = e_hh)))).

tff(f319, type, f319: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f319_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f319(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))))).

tff(f320, type, f320: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f320_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f320(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f321, type, f321: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f321_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f321(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_cc)))).

tff(f322, type, f322: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f322_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f322(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_ee)))).

tff(f323, type, f323: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f323_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f323(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_ff)))).

tff(f324, type, f324: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f324_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f324(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f325, type, f325: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f325_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f325(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_gg)))).

tff(f326, type, f326: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f326_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f326(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f327, type, f327: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f327_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f327(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & (V_jj = e_gg)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_hh)))).

tff(f328, type, f328: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f328_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f328(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & $lesseq($sum($sum(V_ss,1),1),V_qq)))).

tff(f329, type, f329: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f329_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f329(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_ss,1),
  mk(0, 255)))).

tff(f330, type, f330: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f330_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f330(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & $lesseq($sum($sum(V_ss,1),1),V_qq)) & mem(enum_aa, V_jj,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f331, type, f331: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f331_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f331(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & $lesseq($sum($sum(V_ss,1),1),V_qq)) & mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f332, type, f332: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f332_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f332(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ($sum(V_ss,1) = 0))).

tff(f333, type, f333: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f333_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f333(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & $lesseq($sum($sum(V_ss,1),1),V_qq)) & mem(enum_aa, V_jj,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f334, type, f334: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f334_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f334(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference($difference($sum(V_oo,1),1),V_pp) = $sum(V_ss,1)))).

tff(f335, type, f335: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f335_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f335(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_tt,1),$sum($sum(V_ss,1),V_uu)))).

tff(f336, type, f336: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f336_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f336(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_ss,1),V_qq))).

tff(f337, type, f337: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f337_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f337(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)))).

tff(f338, type, f338: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f338_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f338(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & mem(enum_aa, e_ii,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f339, type, f339: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f339_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f339(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & (e_ii = e_cc)))).

tff(f340, type, f340: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f340_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f340(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & (e_ii = e_ee)))).

tff(f341, type, f341: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f341_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f341(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & (e_ii = e_ff)))).

tff(f342, type, f342: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f342_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f342(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & mem(enum_aa, e_ii,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f343, type, f343: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f343_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f343(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & (e_ii = e_gg)))).

tff(f344, type, f344: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f344_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f344(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum(V_ss,1),1))).

tff(f345, type, f345: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f345_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f345(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference($sum(V_oo,1),V_pp) = $sum(V_ss,1)))).

tff(f346, type, f346: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f346_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f346(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & mem(enum_aa, e_ii,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f347, type, f347: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f347_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f347(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($sum(V_ss,1),1),V_qq)) & (e_ii = e_hh)))).

tff(f348, type, f348: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f348_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f348(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))).

tff(f349, type, f349: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f349_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f349(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f350, type, f350: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f350_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f350(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_cc)))).

tff(f351, type, f351: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f351_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f351(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_ee)))).

tff(f352, type, f352: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f352_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f352(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_ff)))).

tff(f353, type, f353: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f353_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f353(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f354, type, f354: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f354_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f354(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f355, type, f355: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f355_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f355(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_hh)))).

tff(f356, type, f356: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f356_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f356(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)))).

tff(f357, type, f357: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f357_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f357(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f358, type, f358: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f358_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f358(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_gg = e_cc)))).

tff(f359, type, f359: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f359_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f359(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_gg = e_ee)))).

tff(f360, type, f360: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f360_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f360(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_gg = e_ff)))).

tff(f361, type, f361: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f361_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f361(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f362, type, f362: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f362_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f362(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f363, type, f363: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f363_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f363(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_gg = e_hh)))).

tff(f364, type, f364: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f364_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f364(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))).

tff(f365, type, f365: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f365_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f365(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f366, type, f366: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f366_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f366(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_cc)))).

tff(f367, type, f367: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f367_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f367(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_ee)))).

tff(f368, type, f368: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f368_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f368(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_ff)))).

tff(f369, type, f369: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f369_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f369(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f370, type, f370: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f370_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f370(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f371, type, f371: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f371_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f371(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_gg = e_hh)))).

tff(f372, type, f372: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f372_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f372(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))))).

tff(f373, type, f373: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f373_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f373(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f374, type, f374: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f374_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f374(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_cc)))).

tff(f375, type, f375: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f375_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f375(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_ee)))).

tff(f376, type, f376: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f376_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f376(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_ff)))).

tff(f377, type, f377: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f377_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f377(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f378, type, f378: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f378_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f378(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_gg)))).

tff(f379, type, f379: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f379_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f379(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f380, type, f380: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f380_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f380(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_hh)))).

tff(f381, type, f381: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f381_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f381(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr))))).

tff(f382, type, f382: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f382_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f382(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr))))).

tff(f383, type, f383: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f383_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f383(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f384, type, f384: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f384_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f384(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & (e_bb = e_cc)))).

tff(f385, type, f385: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f385_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f385(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & (e_bb = e_ee)))).

tff(f386, type, f386: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f386_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f386(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & (e_bb = e_ff)))).

tff(f387, type, f387: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f387_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f387(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f388, type, f388: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f388_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f388(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & (e_bb = e_gg)))).

tff(f389, type, f389: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f389_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f389(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f390, type, f390: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f390_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f390(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)) & ~
  $lesseq($sum($difference(V_oo,V_pp),1),$sum(V_qq,V_rr)))
  & (e_bb = e_hh)))).

tff(f391, type, f391: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f391_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f391(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))).

tff(f392, type, f392: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f392_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f392(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f393, type, f393: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f393_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f393(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_cc)))).

tff(f394, type, f394: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f394_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f394(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_ee)))).

tff(f395, type, f395: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f395_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f395(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_ff)))).

tff(f396, type, f396: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f396_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f396(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f397, type, f397: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f397_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f397(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_gg)))).

tff(f398, type, f398: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f398_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f398(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f399, type, f399: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f399_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f399(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_hh)))).

tff(f400, type, f400: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f400_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f400(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false)))).

tff(f401, type, f401: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f401_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f401(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f402, type, f402: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f402_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f402(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_bb = e_cc)))).

tff(f403, type, f403: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f403_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f403(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_bb = e_ee)))).

tff(f404, type, f404: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f404_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f404(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_bb = e_ff)))).

tff(f405, type, f405: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f405_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f405(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f406, type, f406: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f406_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f406(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_bb = e_gg)))).

tff(f407, type, f407: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f407_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f407(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f408, type, f408: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f408_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f408(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = true)) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))
  & (e_bb = e_hh)))).

tff(f409, type, f409: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f409_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f409(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))).

tff(f410, type, f410: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f410_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f410(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f411, type, f411: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f411_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f411(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_cc)))).

tff(f412, type, f412: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f412_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f412(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_ee)))).

tff(f413, type, f413: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f413_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f413(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_ff)))).

tff(f414, type, f414: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f414_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f414(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f415, type, f415: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f415_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f415(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_gg)))).

tff(f416, type, f416: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f416_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f416(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f417, type, f417: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f417_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f417(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii))
  & (V_kk = false)) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))
  & (e_bb = e_hh)))).

tff(f418, type, f418: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f418_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f418(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))))).

tff(f419, type, f419: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f419_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f419(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)))))).

tff(f420, type, f420: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f420_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f420(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_cc)))).

tff(f421, type, f421: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f421_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f421(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_ee)))).

tff(f422, type, f422: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f422_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f422(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_ff)))).

tff(f423, type, f423: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f423_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f423(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f424, type, f424: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f424_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f424(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_gg)))).

tff(f425, type, f425: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f425_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f425(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & mem(enum_aa, e_bb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))))).

tff(f426, type, f426: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f426_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f426(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = false)) & (V_nn = false))) & ~
  ((((V_kk = true) & (V_ll = true)) & (V_mm = true)) & (V_nn = false))) & ~
  ((((V_kk = false) & (V_ll = true)) & (V_mm = false)) & (V_nn = false)))
  & (e_bb = e_hh)))).

tff(f427, type, f427: (bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool) > $o).

tff(f427_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int, V_oo:
  $int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa, V_bbhh:
  $int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:bool,
  V_bbbb:bool, V_bbaa:bool]: (f427(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> (((((((($true & ~
  (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~
  (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ (V_jj = e_ii)))).

tff(bbjj_582, conjecture, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:
  $int, V_uu:$int, V_tt:$int, V_ss:$int, V_rr:$int, V_qq:$int, V_pp:$int,
  V_oo:$int, V_nn:bool, V_mm:bool, V_ll:bool, V_kk:bool, V_jj:enum_aa,
  V_bbhh:$int, V_bbgg:$int, V_bbff:$int, V_bbee:$int, V_bbdd:$int, V_bbcc:
  bool, V_bbbb:bool, V_bbaa:bool]: ((f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu,
  V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh,
  V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & (f16(V_zz, V_yy,
  V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm,
  V_ll, V_kk, V_jj, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb,
  V_bbaa) & ($true & (f386(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss,
  V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & $true)))) => (f46(V_zz,
  V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn,
  V_mm, V_ll, V_kk, V_jj, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) & $true))).
