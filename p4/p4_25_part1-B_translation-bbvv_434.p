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
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f1_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f1(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((((((((((((((((((((((((((((((((($true
  & (V_bbpp = 0)) & (V_bbqq = 1)) & mem($int, V_bbrr, integer))
  & $lesseq(0,V_bbrr)) & $lesseq(V_bbrr,2147483647)) & mem($int, V_bbss,
  integer)) & $lesseq(0,V_bbss)) & $lesseq(V_bbss,2147483647))
  & mem($int, V_bbtt, integer)) & $lesseq(0,V_bbtt))
  & $lesseq(V_bbtt,2147483647)) & mem($int, V_zz, integer))
  & $lesseq(0,V_zz)) & $lesseq(V_zz,2147483647)) & $lesseq(1,V_zz))
  & $lesseq(V_zz,254)) & (V_zz = V_bbss)) & mem($int, V_yy, integer))
  & $lesseq(0,V_yy)) & $lesseq(V_yy,2147483647)) & $lesseq(1,V_yy))
  & $lesseq(V_yy,254)) & (V_yy = V_bbss)) & mem($int, V_tt, integer))
  & $lesseq(0,V_tt)) & $lesseq(V_tt,2147483647)) & $lesseq(1,V_tt))
  & $lesseq($sum(V_tt,1),2147483647)) & (V_tt = V_bbtt)) & mem($int, V_ww,
  integer)) & $lesseq(0,V_ww)) & $lesseq(V_ww,2147483647)) & $lesseq(2,V_ww))
  & (V_ww = V_bbrr)) & $lesseq($sum(V_ww,V_yy),253))
  & $lesseq($sum($sum(V_ww,V_zz),V_yy),251)) & mem($int, V_xx, integer))
  & $lesseq(0,V_xx)) & $lesseq(V_xx,2147483647)) & $lesseq(1,V_xx))
  & $lesseq($sum(V_xx,1),254)) & (V_xx = V_bbrr)) & $true) & $true))).

tff(f12, type, f12: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f12_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f12(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(0,$difference(V_ww,1)))).

tff(f16, type, f16: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f16_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f16(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((((((((((((((((((((((((((((((($true
  & mem($int, V_kk, mk(0, 255))) & mem($int, V_ll, mk(0, 255)))
  & mem($int, V_mm, mk(0, 255))) & mem($int, V_nn, mk(0, 255)))
  & mem($int, V_uu, integer)) & $lesseq(0,V_uu)) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_vv, integer)) & $lesseq(0,V_vv))
  & (mem(enum_aa, V_jj, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd))) => (V_ll = 0))) & ((V_jj = e_cc)
  => $lesseq(V_kk,V_xx))) & ((V_jj = e_ee) => $lesseq(V_ll,V_zz)))
  & ((V_jj = e_ff) => $lesseq(V_ll,$sum(V_zz,1)))) & (mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff))) => (V_mm = 0))) & (mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff))) => (V_nn = 0))) & ((V_jj = e_gg)
  => $lesseq(V_nn,1))) & ((V_jj = e_gg) => ($difference(V_uu,V_vv) = V_nn)))
  & (mem(enum_aa, V_jj, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh))) => ($lesseq(V_mm,$sum($sum(V_ww,V_yy),1))
  & $lesseq(V_ll,$sum($sum(V_zz,V_mm),2))))) & ((V_jj = e_hh)
  => ((($difference($difference(V_uu,1),V_vv) = V_nn)
  & $lesseq(V_mm,$sum(V_nn,V_yy))) & $lesseq(V_nn,V_ww)))) & $true)
  & mem($int, V_ss, integer)) & $lesseq(0,V_ss)) & $lesseq(V_ss,2147483647))
  & (mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh))) => (V_ss = 0))) & (mem(enum_aa, V_jj,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))
  => $lesseq(V_mm,$sum($sum(V_ww,V_yy),1)))) & ((V_jj = e_hh)
  => ((($difference($difference(V_uu,1),V_vv) = V_nn)
  & $lesseq(V_mm,$sum(V_nn,V_yy))) & $lesseq(V_nn,$difference(V_ww,1)))))
  & ((V_jj = e_ii)
  => (($difference($difference($difference(V_uu,V_vv),V_ww),1) = V_ss)
  & $lesseq(V_ss,V_tt)))) & (V_bbaa = V_kk)) & (V_bbbb = V_ll))
  & (V_bbcc = V_mm)) & (V_bbdd = V_nn)) & (V_bbee = V_oo)) & (V_bbff = V_pp))
  & (V_bbgg = V_qq)) & (V_bbhh = V_rr)) & (V_bbii = V_uu)) & (V_bbjj = V_jj))
  & (V_bbkk = V_vv)))).

tff(f22, type, f22: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f22_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f22(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> mem($int, $sum(V_uu,1), integer))).

tff(f23, type, f23: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f23_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f23(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(0,$sum(V_uu,1)))).

tff(f31, type, f31: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f31_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f31(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($difference($sum(V_uu,1),V_vv),V_ww),1) = 0))).

tff(f52, type, f52: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f52_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f52(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(V_mm,$sum($sum(V_ww,V_yy),1)))).

tff(f54, type, f54: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f54_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f54(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($sum(V_uu,1),1),V_vv) = V_nn))).

tff(f55, type, f55: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f55_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f55(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(V_mm,$sum(V_nn,V_yy)))).

tff(f56, type, f56: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f56_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f56(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(V_nn,$difference(V_ww,1)))).

tff(f58, type, f58: ($int * $int * $int * $int * $int * $int * $int * $int *
  bool * bool * bool * bool * $int * $int * $int * $int * enum_aa * $int *
  $int * $int * $int * $int * bool * bool * bool * bool * $int * enum_aa *
  $int * bool * bool * bool * bool * $int * $int * $int * $int) > $o).

tff(f58_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f58(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($difference($sum(V_uu,1),V_vv),V_ww),1) = V_ss))).

tff(f124, type, f124: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f124_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f124(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($difference($sum(V_uu,1),$sum(V_uu,1)),V_ww),1) = V_ss))).

tff(f145, type, f145: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f145_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f145(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> mem($int, $sum(V_ll,1), mk(0, 255)))).

tff(f147, type, f147: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f147_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f147(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ($sum(V_ll,1) = 0))).

tff(f149, type, f149: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f149_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f149(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_ll,1),V_zz))).

tff(f243, type, f243: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f243_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f243(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> mem($int, $sum(V_mm,1), mk(0, 255)))).

tff(f247, type, f247: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f247_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f247(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ($sum(V_mm,1) = 0))).

tff(f250, type, f250: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f250_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f250(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(V_mm,$sum(V_ww,V_yy)))).

tff(f252, type, f252: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f252_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f252(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_mm,1),$sum(V_nn,V_yy)))).

tff(f280, type, f280: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f280_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f280(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($sum(V_uu,1),1),$sum(V_uu,1)) = 0))).

tff(f281, type, f281: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f281_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f281(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_mm,1),$sum(0,V_yy)))).

tff(f321, type, f321: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f321_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f321(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_mm,1),V_yy))
  & (V_jj = e_gg)) & (V_oo = false)) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false)) & (e_bb = e_hh)))).

tff(f322, type, f322: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f322_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f322(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_mm,1),V_yy))
  & (V_jj = e_gg)) & (V_oo = false)) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false)) & (e_bb = e_ii)))).

tff(f323, type, f323: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f323_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f323(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ii))
  & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false))) & (V_jj = e_gg)))).

tff(f324, type, f324: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f324_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f324(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f325, type, f325: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f325_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f325(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & (e_bb = e_ee)))).

tff(f326, type, f326: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f326_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f326(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f327, type, f327: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f327_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f327(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f328, type, f328: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f328_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f328(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f329, type, f329: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f329_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f329(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & (e_bb = e_hh)))).

tff(f330, type, f330: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f330_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f330(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_gg)) & (e_bb = e_ii)))).

tff(f331, type, f331: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f331_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f331(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)))).

tff(f333, type, f333: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f333_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f333(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false)) & ($lesseq($sum($sum(V_nn,1),1),V_ww)
  | (~ $lesseq($sum($sum(V_nn,1),1),V_ww) & (V_jj = e_ii))))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (((V_jj = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = true)) & (V_rr = false))
  & (((V_jj = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((V_oo = false) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (((V_jj = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | ((((((((V_oo = false) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false)) & ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) => ~
  (V_rr = false))) & ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false))) & ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  => ~ (V_rr = false))) & (V_jj = e_bb))))).

tff(f334, type, f334: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f334_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f334(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> mem($int, $sum(V_nn,1), mk(0, 255)))).

tff(f335, type, f335: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f335_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f335(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, V_jj,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f336, type, f336: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f336_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f336(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f337, type, f337: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f337_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f337(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, V_jj,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f338, type, f338: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f338_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f338(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($sum(V_uu,1),1),V_vv) = $sum(V_nn,1)))).

tff(f339, type, f339: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f339_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f339(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_mm,1),$sum($sum(V_nn,1),V_yy)))).

tff(f340, type, f340: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f340_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f340(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_nn,1),$difference(V_ww,1)))).

tff(f341, type, f341: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f341_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f341(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)))).

tff(f342, type, f342: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f342_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f342(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false)) & (($lesseq($sum($sum(V_nn,1),1),V_ww)
  & (e_ii = V_jj)) | ~ $lesseq($sum($sum(V_nn,1),1),V_ww)))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (((e_ii = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = true)) & (V_rr = false))
  & (((e_ii = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((V_oo = false) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (((e_ii = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | ((((((((V_oo = false) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false)) & ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) => ~
  (V_rr = false))) & ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false))) & ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  => ~ (V_rr = false))) & (e_ii = e_bb))))).

tff(f343, type, f343: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f343_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f343(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_ii,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f344, type, f344: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f344_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f344(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & (e_ii = e_ee)))).

tff(f345, type, f345: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f345_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f345(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_ii,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f346, type, f346: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f346_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f346(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_ii,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f347, type, f347: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f347_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f347(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ $lesseq($sum($sum(V_nn,1),1),V_ww))
  & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & (e_ii = e_hh)))).

tff(f348, type, f348: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f348_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f348(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true)) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)))).

tff(f350, type, f350: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f350_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f350(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_cc)) & (V_jj = e_bb)) & ((((V_kk = 0) & ($sum(V_ll,1) = 0))
  & ($sum(V_mm,1) = 0)) & ((((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)) & (e_gg = e_cc)) | (((((V_oo = true)
  & (V_pp = true)) & (V_qq = false)) => ~ (V_rr = false)) & (e_gg = V_jj)))))
  | (((((((((~ (V_jj = e_bb) & ~ (V_jj = e_ii)) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd))
  & (V_jj = e_cc)) & ((V_kk = $sum(V_kk,1)) & ((((((V_oo = false)
  | (V_pp = false)) | (V_qq = true)) | (V_rr = true)) & (e_gg = e_bb))
  | ((((~ (V_oo = false) & ~ (V_pp = false)) & ~ (V_qq = true)) & ~
  (V_rr = true)) & (((((($lesseq(V_xx,$sum(V_kk,1)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_dd))
  | ((((($lesseq(V_xx,$sum(V_kk,1)) & (V_oo = true)) & (V_pp = true))
  & (V_qq = false)) => ~ (V_rr = false)) & (e_gg = V_jj)))))))
  & ((($sum(V_ll,1) = V_ll) & ($sum(V_mm,1) = V_mm)) & (0 = V_nn))))
  & ($sum(V_uu,1) = V_vv)) | (((~ (V_jj = e_bb) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_ii)) & ((((((((((V_oo = false) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & ((($lesseq($sum($sum(V_nn,1),1),V_ww) & (e_gg = V_jj))
  | (~ $lesseq($sum($sum(V_nn,1),1),V_ww) & (e_gg = e_ii)))
  & (0 = $sum(V_nn,1)))) & ($sum(V_uu,1) = V_vv)) | ((((V_oo = true)
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false))) | ((((V_oo = true)
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false))) | ((((V_oo = false)
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)))
  | (((((((((V_oo = false) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false)) & ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) => ~
  (V_rr = false))) & ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false))) & ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  => ~ (V_rr = false))) & ((e_gg = e_bb) & (0 = $sum(V_nn,1))))
  & ($sum(V_uu,1) = V_vv))))))).

tff(f351, type, f351: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f351_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f351(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f352, type, f352: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f352_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f352(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_ee)))).

tff(f353, type, f353: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f353_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f353(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f354, type, f354: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f354_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f354(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f355, type, f355: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f355_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f355(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f356, type, f356: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f356_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f356(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_hh)))).

tff(f357, type, f357: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f357_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f357(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_ii)))).

tff(f358, type, f358: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f358_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f358(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true)) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false)))).

tff(f359, type, f359: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f359_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f359(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f360, type, f360: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f360_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f360(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & (e_gg = e_ee)))).

tff(f361, type, f361: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f361_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f361(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f362, type, f362: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f362_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f362(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f363, type, f363: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f363_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f363(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f364, type, f364: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f364_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f364(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & (e_gg = e_hh)))).

tff(f365, type, f365: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f365_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f365(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & (e_gg = e_ii)))).

tff(f366, type, f366: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f366_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f366(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false)) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)))).

tff(f367, type, f367: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f367_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f367(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f368, type, f368: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f368_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f368(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_ee)))).

tff(f369, type, f369: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f369_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f369(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f370, type, f370: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f370_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f370(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f371, type, f371: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f371_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f371(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f372, type, f372: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f372_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f372(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_hh)))).

tff(f373, type, f373: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f373_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f373(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & (V_jj = e_hh)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_gg = e_ii)))).

tff(f374, type, f374: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f374_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f374(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false))) & (V_jj = e_hh)))).

tff(f376, type, f376: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f376_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f376(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false)) & (($lesseq($sum($sum(V_nn,1),1),V_ww)
  & (e_bb = V_jj)) | (~ $lesseq($sum($sum(V_nn,1),1),V_ww) & (e_bb = e_ii))))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (((e_bb = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = true)) & (V_rr = false))
  & (((e_bb = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((V_oo = false) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (((e_bb = e_gg) & (V_vv = $sum(V_uu,1))) & ($sum(V_nn,1) = 0))))
  | (((((((V_oo = false) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false)) & ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) => ~
  (V_rr = false))) & ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false))) & ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  => ~ (V_rr = false)))))).

tff(f377, type, f377: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f377_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f377(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f378, type, f378: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f378_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f378(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & (e_bb = e_ee)))).

tff(f379, type, f379: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f379_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f379(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f380, type, f380: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f380_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f380(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f381, type, f381: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f381_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f381(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f382, type, f382: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f382_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f382(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & (e_bb = e_hh)))).

tff(f383, type, f383: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f383_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f383(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ii)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_hh)) & (e_bb = e_ii)))).

tff(f384, type, f384: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f384_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f384(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)))).

tff(f386, type, f386: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f386_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f386(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))
  & ($lesseq($sum($difference(V_uu,V_vv),1),$sum(V_ww,V_tt)) | (~
  $lesseq($sum($difference(V_uu,V_vv),1),$sum(V_ww,V_tt)) & (V_jj = e_bb))))
  | (((((V_oo = true) & (V_pp = true)) & (V_qq = false)) & (V_rr = false))
  & (V_jj = e_bb))) | (((((V_oo = true) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & (V_jj = e_bb))) | (((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)) & (V_jj = e_bb)))
  | ((((((((V_oo = false) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false)) & ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) => ~
  (V_rr = false))) & ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false))) & ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  => ~ (V_rr = false))) & (V_jj = e_bb))))).

tff(f388, type, f388: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f388_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f388(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> mem($int, $sum(V_ss,1), integer))).

tff(f389, type, f389: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f389_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f389(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq(0,$sum(V_ss,1)))).

tff(f390, type, f390: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f390_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f390(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_ss,1),2147483647))).

tff(f391, type, f391: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f391_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f391(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, V_jj,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f392, type, f392: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f392_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f392(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ($sum(V_ss,1) = 0))).

tff(f393, type, f393: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f393_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f393(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa)
  <=> ($difference($difference($difference($sum(V_uu,1),V_vv),V_ww),1) = $sum(V_ss,1)))).

tff(f394, type, f394: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f394_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f394(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> $lesseq($sum(V_ss,1),V_tt))).

tff(f395, type, f395: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f395_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f395(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)))).

tff(f396, type, f396: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f396_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f396(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))
  & (($lesseq($sum($difference(V_uu,V_vv),1),$sum(V_ww,V_tt))
  & (e_bb = V_jj)) | ~
  $lesseq($sum($difference(V_uu,V_vv),1),$sum(V_ww,V_tt))))
  | ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) & (V_rr = false)))
  | ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) & (V_rr = false)))
  | ((((V_oo = false) & (V_pp = true)) & (V_qq = false)) & (V_rr = false)))
  | (((((((V_oo = false) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false)) & ((((V_oo = true) & (V_pp = true)) & (V_qq = false)) => ~
  (V_rr = false))) & ((((V_oo = true) & (V_pp = true)) & (V_qq = true)) => ~
  (V_rr = false))) & ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  => ~ (V_rr = false)))))).

tff(f397, type, f397: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f397_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f397(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f398, type, f398: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f398_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f398(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & (e_bb = e_ee)))).

tff(f399, type, f399: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f399_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f399(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f400, type, f400: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f400_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f400(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f401, type, f401: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f401_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f401(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f402, type, f402: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f402_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f402(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & (e_bb = e_hh)))).

tff(f403, type, f403: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f403_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f403(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ $lesseq($sum(V_ss,2),V_tt))
  & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false)) & (e_bb = e_ii)))).

tff(f404, type, f404: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f404_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f404(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true)) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)))).

tff(f405, type, f405: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f405_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f405(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f406, type, f406: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f406_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f406(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_bb = e_ee)))).

tff(f407, type, f407: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f407_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f407(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f408, type, f408: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f408_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f408(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f409, type, f409: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f409_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f409(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f410, type, f410: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f410_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f410(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_bb = e_hh)))).

tff(f411, type, f411: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f411_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f411(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_bb = e_ii)))).

tff(f412, type, f412: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f412_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f412(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true)) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false)))).

tff(f413, type, f413: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f413_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f413(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f414, type, f414: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f414_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f414(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & (e_bb = e_ee)))).

tff(f415, type, f415: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f415_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f415(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f416, type, f416: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f416_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f416(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f417, type, f417: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f417_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f417(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f418, type, f418: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f418_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f418(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & (e_bb = e_hh)))).

tff(f419, type, f419: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f419_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f419(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = true))
  & (V_pp = true)) & (V_qq = true)) & (V_rr = false)) & (e_bb = e_ii)))).

tff(f420, type, f420: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f420_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f420(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false)) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)))).

tff(f421, type, f421: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f421_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f421(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f422, type, f422: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f422_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f422(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_bb = e_ee)))).

tff(f423, type, f423: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f423_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f423(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f424, type, f424: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f424_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f424(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f425, type, f425: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f425_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f425(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f426, type, f426: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f426_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f426(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_bb = e_hh)))).

tff(f427, type, f427: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f427_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f427(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & (V_jj = e_ii)) & (V_oo = false))
  & (V_pp = true)) & (V_qq = false)) & (V_rr = false)) & (e_bb = e_ii)))).

tff(f428, type, f428: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f428_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f428(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc))
  & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg))
  & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true)) & (V_qq = true))
  & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true)) & (V_qq = false))
  & (V_rr = false))) & (V_jj = e_ii)))).

tff(f429, type, f429: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f429_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f429(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))))).

tff(f430, type, f430: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f430_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f430(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & (e_bb = e_ee)))).

tff(f431, type, f431: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f431_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f431(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)))))).

tff(f432, type, f432: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f432_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f432(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)))))).

tff(f433, type, f433: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f433_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f433(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))))).

tff(f434, type, f434: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f434_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f434(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & (e_bb = e_hh)))).

tff(f435, type, f435: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f435_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f435(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_jj = e_bb)) & ~
  (V_jj = e_cc)) & ~ (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_hh)) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & ~ ((((V_oo = true) & (V_pp = true))
  & (V_qq = true)) & (V_rr = false))) & ~ ((((V_oo = false) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false))) & (V_jj = e_ii)) & (e_bb = e_ii)))).

tff(f436, type, f436: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f436_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f436(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((($true & ~ (V_jj = e_bb)) & ~ (V_jj = e_cc)) & ~
  (V_jj = e_dd)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_gg)) & ~
  (V_jj = e_hh)) & ~ (V_jj = e_ii)))).

tff(f438, type, f438: ($int * $int * $int * $int * $int * $int * $int *
  $int * bool * bool * bool * bool * $int * $int * $int * $int * enum_aa *
  $int * $int * $int * $int * $int * bool * bool * bool * bool * $int *
  enum_aa * $int * bool * bool * bool * bool * $int * $int * $int * $int) >
  $o).

tff(f438_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa, V_bbtt:
  $int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:bool,
  V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa, V_bbii:
  $int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:$int,
  V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: (f438(V_zz, V_yy, V_xx, V_ww, V_vv,
  V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) <=> (((((((((~ (V_jj = e_ii) & ~ (V_jj = e_hh)) & ~
  (V_jj = e_gg)) & ~ (V_jj = e_ff)) & ~ (V_jj = e_ee)) & ~ (V_jj = e_dd)) & ~
  (V_jj = e_cc)) & (V_jj = e_bb)) & (((((V_kk = 0) & (V_ll = 0))
  & (V_mm = 0)) & (V_nn = 0)) & ((((((V_oo = true) & (V_pp = true))
  & (V_qq = false)) & (V_rr = false)) & (V_jj = e_cc)) | ((((V_oo = true)
  & (V_pp = true)) & (V_qq = false)) => ~ (V_rr = false))))) | ~
  (V_jj = e_bb)))).

tff(bbvv_434, conjecture, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:
  $int, V_uu:$int, V_tt:$int, V_ss:$int, V_rr:bool, V_qq:bool, V_pp:bool,
  V_oo:bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:enum_aa,
  V_bbtt:$int, V_bbss:$int, V_bbrr:$int, V_bbqq:$int, V_bbpp:$int, V_bboo:
  bool, V_bbnn:bool, V_bbmm:bool, V_bbll:bool, V_bbkk:$int, V_bbjj:enum_aa,
  V_bbii:$int, V_bbhh:bool, V_bbgg:bool, V_bbff:bool, V_bbee:bool, V_bbdd:
  $int, V_bbcc:$int, V_bbbb:$int, V_bbaa:$int]: ((f1(V_zz, V_yy, V_xx, V_ww,
  V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk,
  V_jj, V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) & (f16(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbtt, V_bbss,
  V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  & ($true & (f323(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr,
  V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & $true))))
  => (f243(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp,
  V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & $true))).
