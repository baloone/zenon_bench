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

tff(f1, type, f1: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f1_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((((((((((((((((((((($true & (V_ccaa = 0))
  & (V_ccbb = 1)) & mem($int, V_cccc, integer)) & $lesseq(0,V_cccc))
  & $lesseq(V_cccc,2147483647)) & mem($int, V_ccdd, integer))
  & $lesseq(0,V_ccdd)) & $lesseq(V_ccdd,2147483647)) & mem($int, V_ccee,
  integer)) & $lesseq(0,V_ccee)) & $lesseq(V_ccee,2147483647))
  & mem($int, V_xx, integer)) & $lesseq(0,V_xx)) & $lesseq(V_xx,2147483647))
  & $lesseq(1,V_xx)) & $lesseq(V_xx,254)) & (V_xx = V_ccdd))
  & mem($int, V_yy, integer)) & $lesseq(0,V_yy)) & $lesseq(V_yy,2147483647))
  & $lesseq(1,V_yy)) & $lesseq(V_yy,254)) & (V_yy = V_ccdd))
  & mem($int, V_zz, integer)) & $lesseq(0,V_zz)) & $lesseq(V_zz,2147483647))
  & $lesseq(1,V_zz)) & $lesseq($sum(V_zz,1),2147483647)) & (V_zz = V_ccee))
  & mem($int, V_vv, integer)) & $lesseq(0,V_vv)) & $lesseq(V_vv,2147483647))
  & $lesseq(2,V_vv)) & (V_vv = V_cccc)) & $lesseq($sum(V_vv,V_yy),253))
  & $lesseq($sum($sum(V_vv,V_xx),V_yy),251)) & mem($int, V_ww, integer))
  & $lesseq(0,V_ww)) & $lesseq(V_ww,2147483647)) & $lesseq(1,V_ww))
  & $lesseq($sum(V_ww,1),254)) & (V_ww = V_cccc)) & $true) & $true))).

tff(f37, type, f37: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f37_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f37(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($sum($difference(V_uu,V_tt),1),V_vv))).

tff(f51, type, f51: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f51_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f51(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & $true) & $true) & $true) & $true) & mem($int, V_oo, integer))
  & $lesseq(0,V_oo)) & mem(set($int), V_rr, power($int, natural)))
  & mem(set($int), V_pp, power($int, natural))) & mem(set($int), V_ss,
  power($int, natural))) & mem(set($int), V_qq, power($int, natural)))
  & ![V_bbmm1:$int]: (((mem($int, V_bbmm1, integer) & $lesseq(0,V_bbmm1))
  & $lesseq($sum(V_oo,1),V_bbmm1)) => ~ mem($int, V_bbmm1, V_rr)))
  & ![V_bbmm1:$int]: (((mem($int, V_bbmm1, integer) & $lesseq(0,V_bbmm1))
  & $lesseq($sum(V_oo,1),V_bbmm1)) => ~ mem($int, V_bbmm1, V_pp)))
  & ![V_bbmm1:$int]: (((mem($int, V_bbmm1, integer) & $lesseq(0,V_bbmm1))
  & $lesseq($sum(V_oo,1),V_bbmm1)) => ~ mem($int, V_bbmm1, V_ss)))
  & ![V_bbmm1:$int]: (((mem($int, V_bbmm1, integer) & $lesseq(0,V_bbmm1))
  & $lesseq($sum(V_oo,1),V_bbmm1)) => ~ mem($int, V_bbmm1, V_qq)))
  & infix_eqeq($int, inter($int, V_pp, V_rr), empty($int)))
  & infix_eqeq($int, inter($int, V_ss, V_rr), empty($int)))
  & infix_eqeq($int, inter($int, V_qq, V_rr), empty($int))) & $true) & $true)
  & mem($int, V_bbkk, integer)) & $lesseq(0,V_bbkk)) & mem($int, V_bbjj,
  integer)) & $lesseq(0,V_bbjj)) & mem($int, V_bbii, integer))
  & $lesseq(0,V_bbii)) & mem($int, V_bbcc, integer)) & $lesseq(0,V_bbcc))
  & mem($int, V_bbhh, integer)) & $lesseq(0,V_bbhh)) & (mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii))) => mem($int, V_bbkk,
  mk(1, V_oo)))) & ((V_bbbb = e_cc) => mem(set($int), mk(V_bbkk, V_oo),
  power($int, V_pp)))) & ((V_bbbb = e_cc)
  => $lesseq($difference($sum(V_oo,1),V_bbkk),V_ww))) & (mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_dd),
  singleton(enum_aa, e_ee)), singleton(enum_aa, e_ff)),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii))) => ((((mem($int, V_bbkk, mk(1, V_oo))
  & mem($int, V_bbjj, mk(V_bbkk, V_oo))) & mem(set($int), mk(V_bbkk, V_bbjj),
  power($int, V_pp))) & ~ mem($int, $sum(V_bbjj,1), V_pp))
  & ($difference(V_bbjj,V_bbkk) = V_ww)))) & ((V_bbbb = e_dd)
  => ((V_bbjj = V_oo) & mem($int, V_oo, V_pp)))) & (mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))
  => ((((mem($int, V_bbkk, mk(1, V_oo)) & mem($int, V_bbjj, mk(V_bbkk,
  V_oo))) & mem(set($int), mk(V_bbkk, V_bbjj), power($int, V_pp)))
  & ($difference(V_bbjj,V_bbkk) = V_ww)) & mem(set($int), mk($sum(V_bbjj,1),
  V_oo), power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq)))))) & ((V_bbbb = e_ee) => ((V_bbii = V_oo)
  & mem(set($int), mk($sum(V_bbjj,1), V_oo), power($int, union($int, V_pp,
  V_qq)))))) & (mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))
  => ((($lesseq($sum(V_bbjj,1),V_oo) & mem($int, V_bbii, mk(V_bbjj, V_oo)))
  & $lesseq($difference($difference(V_bbii,V_bbjj),1),V_xx))
  & mem(set($int), mk($sum(V_bbjj,1), V_bbii), power($int, union($int, V_pp,
  V_qq)))))) & ((V_bbbb = e_ff) => (V_bbcc = V_oo))) & (mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ff),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii))) => (mem($int, V_bbcc, mk(V_bbii, V_oo))
  & mem(set($int), mk($sum(V_bbii,1), V_bbcc), power($int, V_qq)))))
  & ((V_bbbb = e_gg) => mem(set($int), mk($sum(V_bbcc,1), V_oo),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq))))) & ((V_bbbb = e_gg) => ((((mem($int, V_bbhh, mk(V_bbcc, V_oo))
  & mem($int, V_bbhh, mk($difference(V_oo,1), V_oo)))
  & mem(set($int), mk($sum(V_bbcc,1), V_bbhh),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq)))) & mem(set($int), mk($sum(V_bbhh,1), V_oo), power($int, V_rr))) & ~
  mem($int, V_bbhh, V_rr)))) & ((V_bbbb = e_gg) => ~
  mem(set($int), mk($difference(V_oo,1), V_oo), power($int, V_rr))))
  & (mem(enum_aa, V_bbbb, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh))) => ![V_tt1:$int, V_uu1:$int]:
  (((mem($int, V_tt1, mk($sum(V_bbcc,1), V_oo)) & mem($int, V_uu1,
  mk($sum(V_bbcc,1), V_oo))) & mem(set($int), mk(V_tt1, V_uu1),
  power($int, V_rr))) => $lesseq($sum($difference(V_uu1,V_tt1),1),V_vv))))
  & (mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii))) => (~
  mem($int, $sum(V_bbcc,1), V_qq) & $lesseq($sum(V_bbcc,1),V_oo))))
  & (mem(enum_aa, V_bbbb, union(enum_aa, singleton(enum_aa, e_hh),
  singleton(enum_aa, e_ii))) => ((mem($int, V_bbhh, mk(V_bbcc, V_oo))
  & mem(set($int), mk($sum(V_bbhh,1), V_oo), power($int, V_rr)))
  & mem(set($int), mk($sum(V_bbcc,1), V_bbhh),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq)))))) & ((V_bbbb = e_hh) => ($lesseq(V_bbhh,V_oo) & ~
  mem($int, V_bbhh, V_rr)))) & ((V_bbbb = e_hh)
  => $lesseq($difference($difference(V_oo,1),V_bbhh),V_vv)))
  & (mem(enum_aa, V_bbbb, union(enum_aa, singleton(enum_aa, e_hh),
  singleton(enum_aa, e_ii)))
  => $lesseq($difference($difference(V_bbhh,V_bbcc),1),V_yy)))
  & ((V_bbbb = e_ii) => (![V_tt1:$int, V_uu1:$int]: (((mem($int, V_tt1,
  mk($sum(V_bbcc,1), V_bbhh)) & mem($int, V_uu1, mk($sum(V_bbcc,1), V_bbhh)))
  & mem(set($int), mk(V_tt1, V_uu1), power($int, V_rr)))
  => $lesseq($sum($difference(V_uu1,V_tt1),1),V_vv))
  & mem($int, $difference($difference(V_oo,V_bbhh),1), mk(V_vv,
  $sum(V_vv,V_zz)))))) & (V_bbnn = V_bbdd)) & (V_bboo = V_bbee))
  & (V_bbpp = V_bbff)) & (V_bbqq = V_bbgg)) & infix_eqeq($int, V_bbrr, V_rr))
  & infix_eqeq($int, V_bbss, V_pp)) & infix_eqeq($int, V_bbtt, V_ss))
  & infix_eqeq($int, V_bbuu, V_qq)) & (V_bbvv = V_oo)))).

tff(f54, type, f54: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f54_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f54(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((V_bbdd = false) & (V_bbee = true)) & (V_bbff = true))
  & (V_bbgg = false)) | ((((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = false)) & (V_bbgg = false)) & infix_eqeq($int, V_pp,
  union($int, V_pp, singleton($int, $sum(V_oo,1)))))
  & mem($int, $sum(V_oo,1), V_rr))) | ((((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & infix_eqeq($int, V_ss,
  union($int, V_ss, singleton($int, $sum(V_oo,1)))))
  & mem($int, $sum(V_oo,1), V_rr))) | ((((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false))
  & infix_eqeq($int, V_qq, union($int, V_qq, singleton($int, $sum(V_oo,1)))))
  & mem($int, $sum(V_oo,1), V_rr))) | ((((((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) => ~ (V_bbgg = false))
  & ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false)) => ~
  (V_bbgg = false))) & ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) => ~ (V_bbgg = false))) & ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) => ~ (V_bbgg = false)))
  & mem($int, $sum(V_oo,1), V_rr))))).

tff(f56, type, f56: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f56_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f56(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_oo,1), integer))).

tff(f57, type, f57: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f57_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f57(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(0,$sum(V_oo,1)))).

tff(f68, type, f68: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f68_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f68(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, union($int, V_rr,
  singleton($int, $sum(V_oo,1))), V_pp), V_ss), V_qq))))).

tff(f71, type, f71: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f71_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f71(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, V_bbii, mk(V_bbjj, $sum(V_oo,1))))).

tff(f74, type, f74: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f74_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f74(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, V_bbcc, mk(V_bbii, $sum(V_oo,1))))).

tff(f82, type, f82: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f82_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f82(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, V_bbhh, mk(V_bbcc, $sum(V_oo,1))))).

tff(f83, type, f83: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f83_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f83(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbhh,1), $sum(V_oo,1)),
  power($int, union($int, V_rr, singleton($int, $sum(V_oo,1))))))).

tff(f84, type, f84: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f84_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f84(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbcc,1), V_bbhh),
  power($int, union($int, union($int, union($int, union($int, V_rr,
  singleton($int, $sum(V_oo,1))), V_pp), V_ss), V_qq))))).

tff(f97, type, f97: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f97_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f97(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  mem($int, $sum(V_bbjj,1), V_pp))).

tff(f102, type, f102: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f102_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f102(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (V_bbjj = $sum(V_oo,1)))).

tff(f108, type, f108: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f108_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f108(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (V_bbii = $sum(V_oo,1)))).

tff(f110, type, f110: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f110_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f110(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($difference($difference(V_bbii,V_bbjj),1),V_xx))).

tff(f114, type, f114: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f114_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f114(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (V_bbcc = $sum(V_oo,1)))).

tff(f116, type, f116: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f116_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f116(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbii,1), V_bbcc), power($int, V_qq)))).

tff(f121, type, f121: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f121_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f121(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, V_bbhh, mk($difference($sum(V_oo,1),1), $sum(V_oo,1))))).

tff(f123, type, f123: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f123_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f123(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbhh,1), $sum(V_oo,1)), power($int, V_rr)))).

tff(f124, type, f124: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f124_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f124(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  mem($int, V_bbhh, V_rr))).

tff(f126, type, f126: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f126_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f126(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  mem(set($int), mk($difference($sum(V_oo,1),1), $sum(V_oo,1)),
  power($int, V_rr)))).

tff(f129, type, f129: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f129_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f129(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  mem($int, $sum(V_bbcc,1), V_qq))).

tff(f133, type, f133: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f133_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f133(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_bbhh,$sum(V_oo,1)))).

tff(f135, type, f135: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f135_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f135(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($difference($difference($sum(V_oo,1),1),V_bbhh),V_vv))).

tff(f137, type, f137: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f137_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f137(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($difference($difference(V_bbhh,V_bbcc),1),V_yy))).

tff(f141, type, f141: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f141_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f141(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $difference($difference($sum(V_oo,1),V_bbhh),1), mk(V_vv,
  $sum(V_vv,V_zz))))).

tff(f148, type, f148: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f148_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f148(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, V_rr, V_pp),
  union($int, V_ss, singleton($int, $sum(V_oo,1)))), V_qq))))).

tff(f156, type, f156: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f156_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f156(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((V_bbdd = false) & (V_bbee = true)) & (V_bbff = true))
  & (V_bbgg = false)) & infix_eqeq($int, V_rr, union($int, V_rr,
  singleton($int, $sum(V_oo,1))))) | (((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = false)) & (V_bbgg = false)) & infix_eqeq($int, V_pp,
  union($int, V_pp, singleton($int, $sum(V_oo,1)))))) | (((((V_bbdd = true)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & infix_eqeq($int, V_ss, union($int, V_ss,
  singleton($int, $sum(V_oo,1)))))) & mem($int, $sum(V_oo,1), V_qq))
  | ((((V_bbdd = false) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) | ((((((((V_bbdd = false) & (V_bbee = true))
  & (V_bbff = true)) => ~ (V_bbgg = false)) & ((((V_bbdd = true)
  & (V_bbee = true)) & (V_bbff = false)) => ~ (V_bbgg = false)))
  & ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = true)) => ~
  (V_bbgg = false))) & ((((V_bbdd = false) & (V_bbee = true))
  & (V_bbff = false)) => ~ (V_bbgg = false))) & mem($int, $sum(V_oo,1),
  V_qq))))).

tff(f160, type, f160: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f160_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f160(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  union($int, V_qq, singleton($int, $sum(V_oo,1)))))))).

tff(f161, type, f161: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f161_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f161(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), V_bbii),
  power($int, union($int, V_pp, union($int, V_qq,
  singleton($int, $sum(V_oo,1)))))))).

tff(f163, type, f163: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f163_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f163(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbii,1), V_bbcc),
  power($int, union($int, V_qq, singleton($int, $sum(V_oo,1))))))).

tff(f166, type, f166: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f166_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f166(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  (V_bbcc = V_oo))).

tff(f171, type, f171: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f171_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f171(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((V_bbdd = false) & (V_bbee = true)) & (V_bbff = true))
  & (V_bbgg = false)) & infix_eqeq($int, V_rr, union($int, V_rr,
  singleton($int, $sum(V_oo,1))))) | (((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = false)) & (V_bbgg = false)) & infix_eqeq($int, V_pp,
  union($int, V_pp, singleton($int, $sum(V_oo,1)))))) | (((((V_bbdd = true)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & infix_eqeq($int, V_ss, union($int, V_ss,
  singleton($int, $sum(V_oo,1)))))) | (((((V_bbdd = false) & (V_bbee = true))
  & (V_bbff = false)) & (V_bbgg = false)) & infix_eqeq($int, V_qq,
  union($int, V_qq, singleton($int, $sum(V_oo,1))))))
  | (((((((V_bbdd = false) & (V_bbee = true)) & (V_bbff = true)) => ~
  (V_bbgg = false)) & ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = false)) => ~ (V_bbgg = false))) & ((((V_bbdd = true)
  & (V_bbee = true)) & (V_bbff = true)) => ~ (V_bbgg = false)))
  & ((((V_bbdd = false) & (V_bbee = true)) & (V_bbff = false)) => ~
  (V_bbgg = false)))))).

tff(f175, type, f175: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f175_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f175(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq))))).

tff(f182, type, f182: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f182_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f182(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, V_bbkk, mk(1, $sum(V_oo,1))))).

tff(f184, type, f184: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f184_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f184(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk(V_bbkk, $sum(V_oo,1)), power($int, V_pp)))).

tff(f185, type, f185: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f185_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f185(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($difference($sum($sum(V_oo,1),1),V_bbkk),V_ww))).

tff(f187, type, f187: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f187_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f187(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, V_bbjj, mk(V_bbkk, $sum(V_oo,1))))).

tff(f188, type, f188: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f188_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f188(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk(V_bbkk, V_bbjj), power($int, V_pp)))).

tff(f189, type, f189: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f189_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f189(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ($difference(V_bbjj,V_bbkk) = V_ww))).

tff(f191, type, f191: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f191_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f191(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_oo,1), V_pp))).

tff(f194, type, f194: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f194_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f194(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), $sum(V_oo,1)),
  power($int, union($int, V_pp, V_qq))))).

tff(f195, type, f195: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f195_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f195(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), V_bbii),
  power($int, union($int, V_pp, V_qq))))).

tff(f199, type, f199: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f199_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f199(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbcc,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, union($int, V_rr,
  singleton($int, $sum(V_oo,1))), V_pp), V_ss), V_qq))))).

tff(f200, type, f200: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f200_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f200(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  (V_bbhh = $sum(V_oo,1)))).

tff(f201, type, f201: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f201_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f201(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  mem(set($int), mk($difference($sum(V_oo,1),1), $sum(V_oo,1)),
  power($int, union($int, V_rr, singleton($int, $sum(V_oo,1))))))).

tff(f253, type, f253: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f253_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f253(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbcc,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, V_rr, V_pp),
  union($int, V_ss, singleton($int, $sum(V_oo,1)))), V_qq))))).

tff(f267, type, f267: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f267_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f267(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbjj,1), $sum(V_oo,1)),
  power($int, union($int, V_pp, union($int, V_qq,
  singleton($int, $sum(V_oo,1)))))))).

tff(f271, type, f271: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f271_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f271(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbcc,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  union($int, V_qq, singleton($int, $sum(V_oo,1)))))))).

tff(f288, type, f288: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f288_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f288(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbcc,1), $sum(V_oo,1)),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq))))).

tff(f289, type, f289: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f289_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f289(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum(V_bbcc,1), V_bbhh),
  power($int, union($int, union($int, union($int, V_rr, V_pp), V_ss),
  V_qq))))).

tff(f360, type, f360: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f360_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f360(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_oo,1), mk($difference($sum(V_oo,1),1),
  $sum(V_oo,1))))).

tff(f361, type, f361: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f361_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f361(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem(set($int), mk($sum($sum(V_oo,1),1), $sum(V_oo,1)),
  power($int, V_rr)))).

tff(f362, type, f362: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f362_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f362(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) <=> ~
  mem($int, $sum(V_oo,1), V_rr))).

tff(f367, type, f367: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f367_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f367(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq(V_oo,V_oo))).

tff(f368, type, f368: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f368_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f368(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($difference($difference($sum(V_oo,1),1),$sum(V_oo,1)),V_vv))).

tff(f372, type, f372: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f372_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f372(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $difference($difference($sum(V_oo,1),$sum(V_oo,1)),1),
  mk(V_vv, $sum(V_vv,V_zz))))).

tff(f726, type, f726: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f726_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f726(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> mem($int, $sum(V_oo,1), mk(V_bbcc, $sum(V_oo,1))))).

tff(f847, type, f847: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f847_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f847(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> $lesseq($difference($difference($sum(V_oo,1),V_bbcc),1),V_yy))).

tff(f850, type, f850: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f850_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f850(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false)))).

tff(f851, type, f851: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f851_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f851(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f852, type, f852: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f852_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f852(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & (e_gg = e_cc)))).

tff(f853, type, f853: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f853_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f853(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_dd),
  singleton(enum_aa, e_ee)), singleton(enum_aa, e_ff)),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f854, type, f854: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f854_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f854(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & (e_gg = e_dd)))).

tff(f855, type, f855: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f855_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f855(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f856, type, f856: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f856_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f856(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & (e_gg = e_ee)))).

tff(f857, type, f857: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f857_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f857(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & (e_gg = e_ff)))).

tff(f858, type, f858: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f858_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f858(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ff),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f859, type, f859: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f859_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f859(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)))) & mem($int, V_tt, mk($sum(V_bbcc,1),
  $sum(V_oo,1)))) & mem($int, V_uu, mk($sum(V_bbcc,1), $sum(V_oo,1))))
  & mem(set($int), mk(V_tt, V_uu), power($int, V_rr))))).

tff(f860, type, f860: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f860_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f860(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f861, type, f861: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f861_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f861(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & mem(enum_aa, e_gg, union(enum_aa, singleton(enum_aa, e_hh),
  singleton(enum_aa, e_ii)))))).

tff(f862, type, f862: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f862_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f862(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & (e_gg = e_hh)))).

tff(f863, type, f863: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f863_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f863(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false)) & (e_gg = e_ii))
  & mem($int, V_tt, mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem($int, V_uu,
  mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem(set($int), mk(V_tt, V_uu),
  power($int, V_rr))))).

tff(f864, type, f864: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f864_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f864(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh)) & (V_bbdd = true))
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))
  & (e_gg = e_ii)))).

tff(f865, type, f865: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f865_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f865(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)))).

tff(f866, type, f866: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f866_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f866(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f867, type, f867: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f867_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f867(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_cc)))).

tff(f868, type, f868: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f868_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f868(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_dd),
  singleton(enum_aa, e_ee)), singleton(enum_aa, e_ff)),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f869, type, f869: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f869_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f869(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_dd)))).

tff(f870, type, f870: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f870_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f870(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f871, type, f871: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f871_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f871(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_ee)))).

tff(f872, type, f872: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f872_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f872(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_ff)))).

tff(f873, type, f873: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f873_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f873(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ff),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f874, type, f874: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f874_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f874(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh))))
  & mem($int, V_tt, mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem($int, V_uu,
  mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem(set($int), mk(V_tt, V_uu),
  power($int, V_rr))))).

tff(f875, type, f875: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f875_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f875(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f876, type, f876: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f876_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f876(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & mem(enum_aa, e_gg,
  union(enum_aa, singleton(enum_aa, e_hh), singleton(enum_aa, e_ii)))))).

tff(f877, type, f877: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f877_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f877(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_hh)))).

tff(f878, type, f878: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f878_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f878(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_ii)) & mem($int, V_tt, mk($sum(V_bbcc,1),
  $sum(V_oo,1)))) & mem($int, V_uu, mk($sum(V_bbcc,1), $sum(V_oo,1))))
  & mem(set($int), mk(V_tt, V_uu), power($int, V_rr))))).

tff(f879, type, f879: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f879_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f879(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & (V_bbbb = e_hh))
  & (V_bbdd = false)) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false)) & (e_gg = e_ii)))).

tff(f880, type, f880: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f880_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f880(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)))).

tff(f881, type, f881: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f881_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f881(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f882, type, f882: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f882_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f882(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_cc)))).

tff(f883, type, f883: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f883_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f883(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_dd),
  singleton(enum_aa, e_ee)), singleton(enum_aa, e_ff)),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f884, type, f884: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f884_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f884(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_dd)))).

tff(f885, type, f885: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f885_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f885(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f886, type, f886: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f886_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f886(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_ee)))).

tff(f887, type, f887: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f887_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f887(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_ff)))).

tff(f888, type, f888: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f888_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f888(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ff),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f889, type, f889: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f889_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f889(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_gg)))).

tff(f890, type, f890: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f890_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f890(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh))))
  & mem($int, V_tt, mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem($int, V_uu,
  mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem(set($int), mk(V_tt, V_uu),
  power($int, V_rr))))).

tff(f891, type, f891: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f891_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f891(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f892, type, f892: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f892_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f892(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_hh), singleton(enum_aa, e_ii)))))).

tff(f893, type, f893: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f893_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f893(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_hh)))).

tff(f894, type, f894: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f894_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f894(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_ii)) & mem($int, V_tt, mk($sum(V_bbcc,1),
  V_bbhh))) & mem($int, V_uu, mk($sum(V_bbcc,1), V_bbhh)))
  & mem(set($int), mk(V_tt, V_uu), power($int, V_rr))))).

tff(f895, type, f895: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f895_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f895(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_ii)) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = true)) & (V_bbgg = false))) & ~
  ((((V_bbdd = true) & (V_bbee = true)) & (V_bbff = false))
  & (V_bbgg = false))) & ~ ((((V_bbdd = true) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false))) & ~ ((((V_bbdd = false)
  & (V_bbee = true)) & (V_bbff = false)) & (V_bbgg = false)))
  & (V_bbbb = e_hh)) & (e_bb = e_ii)))).

tff(f896, type, f896: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f896_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f896(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)))).

tff(f897, type, f897: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f897_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f897(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f898, type, f898: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f898_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f898(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_dd),
  singleton(enum_aa, e_ee)), singleton(enum_aa, e_ff)),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f899, type, f899: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f899_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f899(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f900, type, f900: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f900_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f900(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ff),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f901, type, f901: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f901_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f901(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh))))
  & mem($int, V_tt, mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem($int, V_uu,
  mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem(set($int), mk(V_tt, V_uu),
  power($int, union($int, V_rr, singleton($int, $sum(V_oo,1)))))))).

tff(f902, type, f902: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f902_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f902(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f903, type, f903: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f903_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f903(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, V_bbbb,
  union(enum_aa, singleton(enum_aa, e_hh), singleton(enum_aa, e_ii)))))).

tff(f904, type, f904: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f904_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f904(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh))
  & $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem($int, V_tt, mk($sum(V_bbcc,1),
  V_bbhh))) & mem($int, V_uu, mk($sum(V_bbcc,1), V_bbhh)))
  & mem(set($int), mk(V_tt, V_uu), power($int, union($int, V_rr,
  singleton($int, $sum(V_oo,1)))))))).

tff(f905, type, f905: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f905_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f905(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)))).

tff(f906, type, f906: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f906_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f906(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f907, type, f907: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f907_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f907(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_cc)))).

tff(f908, type, f908: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f908_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f908(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_dd),
  singleton(enum_aa, e_ee)), singleton(enum_aa, e_ff)),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f909, type, f909: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f909_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f909(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_dd)))).

tff(f910, type, f910: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f910_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f910(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ee),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f911, type, f911: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f911_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f911(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_ee)))).

tff(f912, type, f912: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f912_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f912(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_ff)))).

tff(f913, type, f913: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f913_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f913(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_ff),
  singleton(enum_aa, e_gg)), singleton(enum_aa, e_hh)),
  singleton(enum_aa, e_ii)))))).

tff(f914, type, f914: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f914_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f914(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_gg)))).

tff(f915, type, f915: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f915_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f915(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh))))
  & mem($int, V_tt, mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem($int, V_uu,
  mk($sum(V_bbcc,1), $sum(V_oo,1)))) & mem(set($int), mk(V_tt, V_uu),
  power($int, union($int, V_rr, singleton($int, $sum(V_oo,1)))))))).

tff(f916, type, f916: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f916_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f916(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, union(enum_aa, singleton(enum_aa, e_gg),
  singleton(enum_aa, e_hh)), singleton(enum_aa, e_ii)))))).

tff(f917, type, f917: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f917_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f917(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & mem(enum_aa, e_bb,
  union(enum_aa, singleton(enum_aa, e_hh), singleton(enum_aa, e_ii)))))).

tff(f918, type, f918: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f918_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f918(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_hh)))).

tff(f919, type, f919: ($int * $int * $int * $int * $int * $int * $int *
  set($int) * set($int) * set($int) * set($int) * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * bool * bool * bool *
  bool * $int * set($int) * set($int) * set($int) * set($int) * bool * bool *
  bool * bool * $int * $int * $int * $int * $int * $int * bool * bool *
  bool * bool * $int * enum_aa * bool) > $o).

tff(f919_def, axiom, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:set($int), V_pp:
  set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:
  $int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int, V_ccaa:$int,
  V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:$int, V_bbuu:
  set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:set($int), V_bbqq:
  bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:bool, V_bbff:
  bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa, V_bbaa:bool]:
  (f919(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb, V_ccaa,
  V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss, V_bbrr,
  V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii,
  V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((($true & ~ (V_bbbb = e_bb)) & ~ (V_bbbb = e_cc)) & ~
  (V_bbbb = e_dd)) & ~ (V_bbbb = e_ee)) & ~ (V_bbbb = e_ff)) & ~
  (V_bbbb = e_gg)) & ~ (V_bbbb = e_hh)) & ~
  $lesseq($sum($difference(V_oo,V_bbhh),1),$sum(V_vv,V_zz)))
  & (V_bbbb = e_ii)) & (V_bbdd = false)) & (V_bbee = true))
  & (V_bbff = true)) & (V_bbgg = false)) & (e_bb = e_ii)) & mem($int, V_tt,
  mk($sum(V_bbcc,1), V_bbhh))) & mem($int, V_uu, mk($sum(V_bbcc,1), V_bbhh)))
  & mem(set($int), mk(V_tt, V_uu), power($int, union($int, V_rr,
  singleton($int, $sum(V_oo,1)))))))).

tff(ccgg_1970, conjecture, ![V_zz:$int, V_yy:$int, V_xx:$int, V_ww:$int,
  V_vv:$int, V_uu:$int, V_tt:$int, V_ss:set($int), V_rr:set($int), V_qq:
  set($int), V_pp:set($int), V_oo:$int, V_nn:$int, V_mm:$int, V_ll:$int,
  V_kk:$int, V_jj:$int, V_ccee:$int, V_ccdd:$int, V_cccc:$int, V_ccbb:$int,
  V_ccaa:$int, V_bbzz:bool, V_bbyy:bool, V_bbxx:bool, V_bbww:bool, V_bbvv:
  $int, V_bbuu:set($int), V_bbtt:set($int), V_bbss:set($int), V_bbrr:
  set($int), V_bbqq:bool, V_bbpp:bool, V_bboo:bool, V_bbnn:bool, V_bbmm:$int,
  V_bbll:$int, V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:
  bool, V_bbff:bool, V_bbee:bool, V_bbdd:bool, V_bbcc:$int, V_bbbb:enum_aa,
  V_bbaa:bool]: ((f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr,
  V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc,
  V_ccbb, V_ccaa, V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt,
  V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk,
  V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb,
  V_bbaa) & (f51(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq,
  V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc, V_ccbb,
  V_ccaa, V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt, V_bbss,
  V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj,
  V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa)
  & ($true & (f898(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr,
  V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd, V_cccc,
  V_ccbb, V_ccaa, V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu, V_bbtt,
  V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk,
  V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb,
  V_bbaa) & $true)))) => (f182(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_ccee, V_ccdd,
  V_cccc, V_ccbb, V_ccaa, V_bbzz, V_bbyy, V_bbxx, V_bbww, V_bbvv, V_bbuu,
  V_bbtt, V_bbss, V_bbrr, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) & $true))).
