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

tff(f1, type, f1: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f1_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f1(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> (((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem(set(tuple2($int, $int)), V_OBF__iibb,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__jjbb,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__oo, V_OBF__pp), V_OBF__ee))))
  & mem(set(tuple2($int, $int)), V_OBF__kkbb,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__llbb,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__mmbb,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__nnbb,
  union(tuple2(tuple2(tuple2($int, $int), $int), $int), union(tuple2(
                                                              tuple2(
                                                              tuple2($int,
                                                              $int), $int),
                                                              $int), union(
  tuple2(tuple2(tuple2($int, $int), $int), $int), union(tuple2(tuple2(
                                                               tuple2($int,
                                                               $int), $int),
                                                        $int), union(
  tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(tuple2($int,
                                                               $int),
                                                        $int),
  $int, times(tuple2($int, $int), $int, V_OBF__iibb, V_OBF__ee),
  singleton($int, V_OBF__ff)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__jjbb, singleton($int, V_OBF__hh))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__kkbb, V_OBF__ee), singleton($int, V_OBF__jj))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__llbb, V_OBF__ee), singleton($int, V_OBF__ll))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__mmbb, V_OBF__ee), singleton($int, V_OBF__nn))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__oo, V_OBF__pp), V_OBF__ee),
  singleton($int, V_OBF__bb))))) & $true)
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__nnbb,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__oo,
  V_OBF__pp), V_OBF__ee), V_OBF__qq)))) & mem($int, V_OBF__ff, V_OBF__qq))
  & mem($int, V_OBF__hh, V_OBF__qq)) & mem($int, V_OBF__jj, V_OBF__qq))
  & mem($int, V_OBF__ll, V_OBF__qq)) & mem($int, V_OBF__nn, V_OBF__qq))
  & mem($int, V_OBF__bb, V_OBF__qq)) & ~ (V_OBF__ff = V_OBF__hh)) & ~
  (V_OBF__ff = V_OBF__jj)) & ~ (V_OBF__ff = V_OBF__ll)) & ~
  (V_OBF__ff = V_OBF__nn)) & ~ (V_OBF__ff = V_OBF__bb)) & ~
  (V_OBF__hh = V_OBF__ff)) & ~ (V_OBF__hh = V_OBF__jj)) & ~
  (V_OBF__hh = V_OBF__ll)) & ~ (V_OBF__hh = V_OBF__nn)) & ~
  (V_OBF__hh = V_OBF__bb)) & ~ (V_OBF__jj = V_OBF__ff)) & ~
  (V_OBF__jj = V_OBF__hh)) & ~ (V_OBF__jj = V_OBF__ll)) & ~
  (V_OBF__jj = V_OBF__nn)) & ~ (V_OBF__jj = V_OBF__bb)) & ~
  (V_OBF__ll = V_OBF__ff)) & ~ (V_OBF__ll = V_OBF__hh)) & ~
  (V_OBF__ll = V_OBF__jj)) & ~ (V_OBF__ll = V_OBF__nn)) & ~
  (V_OBF__ll = V_OBF__bb)) & ~ (V_OBF__nn = V_OBF__ff)) & ~
  (V_OBF__nn = V_OBF__hh)) & ~ (V_OBF__nn = V_OBF__jj)) & ~
  (V_OBF__nn = V_OBF__ll)) & ~ (V_OBF__nn = V_OBF__bb)) & ~
  (V_OBF__bb = V_OBF__ff)) & ~ (V_OBF__bb = V_OBF__hh)) & ~
  (V_OBF__bb = V_OBF__jj)) & ~ (V_OBF__bb = V_OBF__ll)) & ~
  (V_OBF__bb = V_OBF__nn)) & mem(set($int), V_OBF__oo,
  finite_subsets($int, integer))) & ~ infix_eqeq($int, V_OBF__oo,
  empty($int))) & mem(set($int), V_OBF__pp, finite_subsets($int, integer)))
  & ~ infix_eqeq($int, V_OBF__pp, empty($int))) & mem(set($int), V_OBF__ee,
  finite_subsets($int, integer))) & ~ infix_eqeq($int, V_OBF__ee,
  empty($int))) & mem(set($int), V_OBF__qq, finite_subsets($int, integer)))
  & ~ infix_eqeq($int, V_OBF__qq, empty($int))))).

tff(f2, type, f2: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f2_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f2(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> (((((((((((((((((((($true & mem($int, V_OBF__cc, integer))
  & mem($int, V_OBF__rr, V_OBF__oo)) & mem($int, V_OBF__ss, V_OBF__pp))
  & mem($int, V_OBF__zz, V_OBF__ee)) & mem($int, V_OBF__aa, V_OBF__qq))
  & $true)
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aabb,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__oo,
  V_OBF__pp), V_OBF__ee), V_OBF__qq)))) & $true)
  & mem(set(tuple2($int, $int)), V_OBF__dd,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__gg,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__oo, V_OBF__pp), V_OBF__ee))))
  & mem(set(tuple2($int, $int)), V_OBF__xx,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__vv,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__tt,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__aabb,
  union(tuple2(tuple2(tuple2($int, $int), $int), $int), union(tuple2(
                                                              tuple2(
                                                              tuple2($int,
                                                              $int), $int),
                                                              $int), union(
  tuple2(tuple2(tuple2($int, $int), $int), $int), union(tuple2(tuple2(
                                                               tuple2($int,
                                                               $int), $int),
                                                        $int), union(
  tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(tuple2($int,
                                                               $int),
                                                        $int),
  $int, times(tuple2($int, $int), $int, V_OBF__dd, V_OBF__ee),
  singleton($int, V_OBF__ff)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__gg, singleton($int, V_OBF__hh))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__xx, V_OBF__ee), singleton($int, V_OBF__jj))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__vv, V_OBF__ee), singleton($int, V_OBF__ll))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__tt, V_OBF__ee), singleton($int, V_OBF__nn))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__oo, V_OBF__pp), V_OBF__ee),
  singleton($int, V_OBF__bb))))) & (V_OBF__ccbb = V_OBF__cc))
  & (V_OBF__ddbb = V_OBF__rr)) & (V_OBF__eebb = V_OBF__ss))
  & (V_OBF__ffbb = V_OBF__zz)) & (V_OBF__ggbb = V_OBF__aa))
  & (V_OBF__hhbb = V_OBF__bbbb)))).

tff(f3, type, f3: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f3_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f3(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> ((((((($true
  & ((V_OBF__aa = V_OBF__ff) => ~ mem(tuple2($int, $int), tuple21($int,
  $int, V_OBF__rr, V_OBF__ss), V_OBF__dd))) & ((V_OBF__aa = V_OBF__hh) => ~
  mem(tuple2(tuple2($int, $int), $int), tuple21($int,
  tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss), V_OBF__zz),
  V_OBF__gg))) & ((V_OBF__aa = V_OBF__jj) => ~
  mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__xx))) & ((V_OBF__aa = V_OBF__ll) => ~
  mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__vv))) & ((V_OBF__aa = V_OBF__nn) => ~
  mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__tt))) & ~ (V_OBF__aa = V_OBF__bb)) & (V_OBF__cc = 2)))).

tff(f5, type, f5: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f5_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f5(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> ~
  mem(tuple2(tuple2(tuple2($int, $int), $int), $int), tuple21($int,
  tuple2(tuple2($int, $int), $int), tuple21($int,
  tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss), V_OBF__zz),
  V_OBF__aa), V_OBF__aabb))).

tff(f6, type, f6: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f6_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f6(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> ((($true
  & mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__dd)) & (V_OBF__cc = 2)) & (V_OBF__aa = V_OBF__ff)))).

tff(f7, type, f7: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f7_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f7(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> mem(tuple2(tuple2(tuple2($int, $int), $int), $int), tuple21($int,
  tuple2(tuple2($int, $int), $int), tuple21($int,
  tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss), V_OBF__zz),
  V_OBF__aa), V_OBF__aabb))).

tff(f9, type, f9: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f9_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f9(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> (((((($true
  & mem(tuple2(tuple2($int, $int), $int), tuple21($int,
  tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss), V_OBF__zz),
  V_OBF__gg)) & mem(set(tuple2($int, $int)), V_OBF__ww, relation($int,
  $int, V_OBF__oo, V_OBF__pp)))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__yy,
  relation(tuple2($int, $int), $int, times($int, $int, V_OBF__oo, V_OBF__pp),
  V_OBF__ee))) & mem(set(tuple2($int, $int)), V_OBF__ii, relation($int,
  $int, V_OBF__oo, V_OBF__pp))) & (V_OBF__cc = 2))
  & (V_OBF__aa = V_OBF__hh)))).

tff(f12, type, f12: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f12_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f12(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> mem(set(tuple2($int, $int)), V_OBF__ww,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))).

tff(f14, type, f14: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f14_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f14(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__yy,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__oo, V_OBF__pp), V_OBF__ee))))).

tff(f16, type, f16: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f16_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f16(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> mem(set(tuple2($int, $int)), V_OBF__ii,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))).

tff(f17, type, f17: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f17_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f17(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> (((((((($true
  & mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__xx)) & mem($int, V_OBF__uu, V_OBF__pp))
  & mem(set(tuple2($int, $int)), V_OBF__ww, relation($int, $int, V_OBF__oo,
  V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__ii, relation($int,
  $int, V_OBF__oo, V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__kk,
  relation($int, $int, V_OBF__oo, V_OBF__pp)))
  & mem(set(tuple2($int, $int)), V_OBF__mm, relation($int, $int, V_OBF__oo,
  V_OBF__pp))) & (V_OBF__cc = 2)) & (V_OBF__aa = V_OBF__jj)))).

tff(f20, type, f20: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f20_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f20(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> mem(set(tuple2($int, $int)), V_OBF__kk,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))).

tff(f22, type, f22: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f22_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f22(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  <=> mem(set(tuple2($int, $int)), V_OBF__mm,
  power(tuple2($int, $int), times($int, $int, V_OBF__oo, V_OBF__pp))))).

tff(f23, type, f23: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f23_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f23(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> ((((((($true
  & mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__vv)) & mem(set(tuple2($int, $int)), V_OBF__ww, relation($int,
  $int, V_OBF__oo, V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__ii,
  relation($int, $int, V_OBF__oo, V_OBF__pp)))
  & mem(set(tuple2($int, $int)), V_OBF__kk, relation($int, $int, V_OBF__oo,
  V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__mm, relation($int,
  $int, V_OBF__oo, V_OBF__pp))) & (V_OBF__cc = 2))
  & (V_OBF__aa = V_OBF__ll)))).

tff(f24, type, f24: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f24_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f24(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> ((((((($true
  & mem(tuple2($int, $int), tuple21($int, $int, V_OBF__rr, V_OBF__ss),
  V_OBF__tt)) & mem($int, V_OBF__uu, V_OBF__pp))
  & mem(set(tuple2($int, $int)), V_OBF__ii, relation($int, $int, V_OBF__oo,
  V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__kk, relation($int,
  $int, V_OBF__oo, V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__mm,
  relation($int, $int, V_OBF__oo, V_OBF__pp))) & (V_OBF__cc = 2))
  & (V_OBF__aa = V_OBF__nn)))).

tff(f26, type, f26: ($int * set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set($int) * set($int) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, $int), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * bool * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int * set($int) *
  $int * set(tuple2($int, $int)) * $int * $int * bool * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int) > $o).

tff(f26_def, axiom, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  (f26(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) <=> (($true
  & (V_OBF__aa = V_OBF__bb)) & (V_OBF__cc = 2)))).

tff(oBF__ppbb_1, conjecture, ![V_OBF__zz:$int, V_OBF__yy:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xx:set(tuple2($int, $int)),
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vv:set(tuple2($int, $int)),
  V_OBF__uu:$int, V_OBF__tt:set(tuple2($int, $int)), V_OBF__ss:$int,
  V_OBF__rr:$int, V_OBF__qq:set($int), V_OBF__pp:set($int), V_OBF__oo:
  set($int), V_OBF__nnbb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__nn:$int, V_OBF__mmbb:set(tuple2($int, $int)), V_OBF__mm:
  set(tuple2($int, $int)), V_OBF__llbb:set(tuple2($int, $int)), V_OBF__ll:
  $int, V_OBF__kkbb:set(tuple2($int, $int)), V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjbb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__jj:$int, V_OBF__iibb:set(tuple2($int, $int)), V_OBF__ii:
  set(tuple2($int, $int)), V_OBF__hhbb:bool, V_OBF__hh:$int, V_OBF__ggbb:
  $int, V_OBF__gg:set(tuple2(tuple2($int, $int), $int)), V_OBF__ffbb:$int,
  V_OBF__ff:$int, V_OBF__eebb:$int, V_OBF__ee:set($int), V_OBF__ddbb:$int,
  V_OBF__dd:set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__cc:$int,
  V_OBF__bbbb:bool, V_OBF__bb:$int, V_OBF__aabb:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__aa:$int]:
  ((f1(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu,
  V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff,
  V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc,
  V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa) & (f2(V_OBF__zz, V_OBF__yy,
  V_OBF__xx, V_OBF__ww, V_OBF__vv, V_OBF__uu, V_OBF__tt, V_OBF__ss,
  V_OBF__rr, V_OBF__qq, V_OBF__pp, V_OBF__oo, V_OBF__nnbb, V_OBF__nn,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llbb, V_OBF__ll, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjbb, V_OBF__jj, V_OBF__iibb, V_OBF__ii, V_OBF__hhbb, V_OBF__hh,
  V_OBF__ggbb, V_OBF__gg, V_OBF__ffbb, V_OBF__ff, V_OBF__eebb, V_OBF__ee,
  V_OBF__ddbb, V_OBF__dd, V_OBF__ccbb, V_OBF__cc, V_OBF__bbbb, V_OBF__bb,
  V_OBF__aabb, V_OBF__aa) & ($true & (f6(V_OBF__zz, V_OBF__yy, V_OBF__xx,
  V_OBF__ww, V_OBF__vv, V_OBF__uu, V_OBF__tt, V_OBF__ss, V_OBF__rr,
  V_OBF__qq, V_OBF__pp, V_OBF__oo, V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb,
  V_OBF__mm, V_OBF__llbb, V_OBF__ll, V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb,
  V_OBF__jj, V_OBF__iibb, V_OBF__ii, V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb,
  V_OBF__gg, V_OBF__ffbb, V_OBF__ff, V_OBF__eebb, V_OBF__ee, V_OBF__ddbb,
  V_OBF__dd, V_OBF__ccbb, V_OBF__cc, V_OBF__bbbb, V_OBF__bb, V_OBF__aabb,
  V_OBF__aa) & $true)))) => (f7(V_OBF__zz, V_OBF__yy, V_OBF__xx, V_OBF__ww,
  V_OBF__vv, V_OBF__uu, V_OBF__tt, V_OBF__ss, V_OBF__rr, V_OBF__qq,
  V_OBF__pp, V_OBF__oo, V_OBF__nnbb, V_OBF__nn, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llbb, V_OBF__ll, V_OBF__kkbb, V_OBF__kk, V_OBF__jjbb, V_OBF__jj,
  V_OBF__iibb, V_OBF__ii, V_OBF__hhbb, V_OBF__hh, V_OBF__ggbb, V_OBF__gg,
  V_OBF__ffbb, V_OBF__ff, V_OBF__eebb, V_OBF__ee, V_OBF__ddbb, V_OBF__dd,
  V_OBF__ccbb, V_OBF__cc, V_OBF__bbbb, V_OBF__bb, V_OBF__aabb, V_OBF__aa)
  & $true))).
