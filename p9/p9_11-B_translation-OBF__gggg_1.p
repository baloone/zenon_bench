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

tff(enum_OBF__aa, type, enum_OBF__aa: $tType).

tff(e_OBF__bb, type, e_OBF__bb: enum_OBF__aa).

tff(e_OBF__cc, type, e_OBF__cc: enum_OBF__aa).

tff(e_OBF__dd, type, e_OBF__dd: enum_OBF__aa).

tff(e_OBF__ee, type, e_OBF__ee: enum_OBF__aa).

tff(e_OBF__ff, type, e_OBF__ff: enum_OBF__aa).

tff(e_OBF__gg, type, e_OBF__gg: enum_OBF__aa).

tff(e_OBF__hh, type, e_OBF__hh: enum_OBF__aa).

tff(match_enum_OBF__aa, type, match_enum_OBF__aa: !>[A : $tType]:
  ((enum_OBF__aa * A * A * A * A * A * A * A) > A)).

tff(match_enum_OBF__aa_E_OBF__bb, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__bb, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z)).

tff(match_enum_OBF__aa_E_OBF__cc, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__cc, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z1)).

tff(match_enum_OBF__aa_E_OBF__dd, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__dd, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z2)).

tff(match_enum_OBF__aa_E_OBF__ee, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__ee, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z3)).

tff(match_enum_OBF__aa_E_OBF__ff, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__ff, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z4)).

tff(match_enum_OBF__aa_E_OBF__gg, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__gg, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z5)).

tff(match_enum_OBF__aa_E_OBF__hh, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A]: (match_enum_OBF__aa(A, e_OBF__hh, Z, Z1, Z2, Z3,
  Z4, Z5, Z6) = Z6)).

tff(e_OBF__bb_E_OBF__cc, axiom, ~ (e_OBF__bb = e_OBF__cc)).

tff(e_OBF__bb_E_OBF__dd, axiom, ~ (e_OBF__bb = e_OBF__dd)).

tff(e_OBF__bb_E_OBF__ee, axiom, ~ (e_OBF__bb = e_OBF__ee)).

tff(e_OBF__bb_E_OBF__ff, axiom, ~ (e_OBF__bb = e_OBF__ff)).

tff(e_OBF__bb_E_OBF__gg, axiom, ~ (e_OBF__bb = e_OBF__gg)).

tff(e_OBF__bb_E_OBF__hh, axiom, ~ (e_OBF__bb = e_OBF__hh)).

tff(e_OBF__cc_E_OBF__dd, axiom, ~ (e_OBF__cc = e_OBF__dd)).

tff(e_OBF__cc_E_OBF__ee, axiom, ~ (e_OBF__cc = e_OBF__ee)).

tff(e_OBF__cc_E_OBF__ff, axiom, ~ (e_OBF__cc = e_OBF__ff)).

tff(e_OBF__cc_E_OBF__gg, axiom, ~ (e_OBF__cc = e_OBF__gg)).

tff(e_OBF__cc_E_OBF__hh, axiom, ~ (e_OBF__cc = e_OBF__hh)).

tff(e_OBF__dd_E_OBF__ee, axiom, ~ (e_OBF__dd = e_OBF__ee)).

tff(e_OBF__dd_E_OBF__ff, axiom, ~ (e_OBF__dd = e_OBF__ff)).

tff(e_OBF__dd_E_OBF__gg, axiom, ~ (e_OBF__dd = e_OBF__gg)).

tff(e_OBF__dd_E_OBF__hh, axiom, ~ (e_OBF__dd = e_OBF__hh)).

tff(e_OBF__ee_E_OBF__ff, axiom, ~ (e_OBF__ee = e_OBF__ff)).

tff(e_OBF__ee_E_OBF__gg, axiom, ~ (e_OBF__ee = e_OBF__gg)).

tff(e_OBF__ee_E_OBF__hh, axiom, ~ (e_OBF__ee = e_OBF__hh)).

tff(e_OBF__ff_E_OBF__gg, axiom, ~ (e_OBF__ff = e_OBF__gg)).

tff(e_OBF__ff_E_OBF__hh, axiom, ~ (e_OBF__ff = e_OBF__hh)).

tff(e_OBF__gg_E_OBF__hh, axiom, ~ (e_OBF__gg = e_OBF__hh)).

tff(enum_OBF__aa_inversion, axiom, ![U:enum_OBF__aa]: (((((((U = e_OBF__bb)
  | (U = e_OBF__cc)) | (U = e_OBF__dd)) | (U = e_OBF__ee)) | (U = e_OBF__ff))
  | (U = e_OBF__gg)) | (U = e_OBF__hh))).

tff(set_enum_OBF__aa, type, set_enum_OBF__aa: set(enum_OBF__aa)).

tff(set_enum_OBF__aa_axiom, axiom, ![X:enum_OBF__aa]: mem(enum_OBF__aa, X,
  set_enum_OBF__aa)).

tff(enum_OBF__ii, type, enum_OBF__ii: $tType).

tff(e_OBF__jj, type, e_OBF__jj: enum_OBF__ii).

tff(e_OBF__kk, type, e_OBF__kk: enum_OBF__ii).

tff(e_OBF__ll, type, e_OBF__ll: enum_OBF__ii).

tff(e_OBF__mm, type, e_OBF__mm: enum_OBF__ii).

tff(e_OBF__nn, type, e_OBF__nn: enum_OBF__ii).

tff(e_OBF__oo, type, e_OBF__oo: enum_OBF__ii).

tff(e_OBF__pp, type, e_OBF__pp: enum_OBF__ii).

tff(e_OBF__qq, type, e_OBF__qq: enum_OBF__ii).

tff(e_OBF__rr, type, e_OBF__rr: enum_OBF__ii).

tff(e_OBF__ss, type, e_OBF__ss: enum_OBF__ii).

tff(match_enum_OBF__ii, type, match_enum_OBF__ii: !>[A : $tType]:
  ((enum_OBF__ii * A * A * A * A * A * A * A * A * A * A) > A)).

tff(match_enum_OBF__ii_E_OBF__jj, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__jj, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z)).

tff(match_enum_OBF__ii_E_OBF__kk, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__kk, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z1)).

tff(match_enum_OBF__ii_E_OBF__ll, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__ll, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z2)).

tff(match_enum_OBF__ii_E_OBF__mm, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__mm, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z3)).

tff(match_enum_OBF__ii_E_OBF__nn, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__nn, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z4)).

tff(match_enum_OBF__ii_E_OBF__oo, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__oo, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z5)).

tff(match_enum_OBF__ii_E_OBF__pp, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__pp, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z6)).

tff(match_enum_OBF__ii_E_OBF__qq, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__qq, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z7)).

tff(match_enum_OBF__ii_E_OBF__rr, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__rr, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z8)).

tff(match_enum_OBF__ii_E_OBF__ss, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A,
  Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A, Z9:A]:
  (match_enum_OBF__ii(A, e_OBF__ss, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8,
  Z9) = Z9)).

tff(e_OBF__jj_E_OBF__kk, axiom, ~ (e_OBF__jj = e_OBF__kk)).

tff(e_OBF__jj_E_OBF__ll, axiom, ~ (e_OBF__jj = e_OBF__ll)).

tff(e_OBF__jj_E_OBF__mm, axiom, ~ (e_OBF__jj = e_OBF__mm)).

tff(e_OBF__jj_E_OBF__nn, axiom, ~ (e_OBF__jj = e_OBF__nn)).

tff(e_OBF__jj_E_OBF__oo, axiom, ~ (e_OBF__jj = e_OBF__oo)).

tff(e_OBF__jj_E_OBF__pp, axiom, ~ (e_OBF__jj = e_OBF__pp)).

tff(e_OBF__jj_E_OBF__qq, axiom, ~ (e_OBF__jj = e_OBF__qq)).

tff(e_OBF__jj_E_OBF__rr, axiom, ~ (e_OBF__jj = e_OBF__rr)).

tff(e_OBF__jj_E_OBF__ss, axiom, ~ (e_OBF__jj = e_OBF__ss)).

tff(e_OBF__kk_E_OBF__ll, axiom, ~ (e_OBF__kk = e_OBF__ll)).

tff(e_OBF__kk_E_OBF__mm, axiom, ~ (e_OBF__kk = e_OBF__mm)).

tff(e_OBF__kk_E_OBF__nn, axiom, ~ (e_OBF__kk = e_OBF__nn)).

tff(e_OBF__kk_E_OBF__oo, axiom, ~ (e_OBF__kk = e_OBF__oo)).

tff(e_OBF__kk_E_OBF__pp, axiom, ~ (e_OBF__kk = e_OBF__pp)).

tff(e_OBF__kk_E_OBF__qq, axiom, ~ (e_OBF__kk = e_OBF__qq)).

tff(e_OBF__kk_E_OBF__rr, axiom, ~ (e_OBF__kk = e_OBF__rr)).

tff(e_OBF__kk_E_OBF__ss, axiom, ~ (e_OBF__kk = e_OBF__ss)).

tff(e_OBF__ll_E_OBF__mm, axiom, ~ (e_OBF__ll = e_OBF__mm)).

tff(e_OBF__ll_E_OBF__nn, axiom, ~ (e_OBF__ll = e_OBF__nn)).

tff(e_OBF__ll_E_OBF__oo, axiom, ~ (e_OBF__ll = e_OBF__oo)).

tff(e_OBF__ll_E_OBF__pp, axiom, ~ (e_OBF__ll = e_OBF__pp)).

tff(e_OBF__ll_E_OBF__qq, axiom, ~ (e_OBF__ll = e_OBF__qq)).

tff(e_OBF__ll_E_OBF__rr, axiom, ~ (e_OBF__ll = e_OBF__rr)).

tff(e_OBF__ll_E_OBF__ss, axiom, ~ (e_OBF__ll = e_OBF__ss)).

tff(e_OBF__mm_E_OBF__nn, axiom, ~ (e_OBF__mm = e_OBF__nn)).

tff(e_OBF__mm_E_OBF__oo, axiom, ~ (e_OBF__mm = e_OBF__oo)).

tff(e_OBF__mm_E_OBF__pp, axiom, ~ (e_OBF__mm = e_OBF__pp)).

tff(e_OBF__mm_E_OBF__qq, axiom, ~ (e_OBF__mm = e_OBF__qq)).

tff(e_OBF__mm_E_OBF__rr, axiom, ~ (e_OBF__mm = e_OBF__rr)).

tff(e_OBF__mm_E_OBF__ss, axiom, ~ (e_OBF__mm = e_OBF__ss)).

tff(e_OBF__nn_E_OBF__oo, axiom, ~ (e_OBF__nn = e_OBF__oo)).

tff(e_OBF__nn_E_OBF__pp, axiom, ~ (e_OBF__nn = e_OBF__pp)).

tff(e_OBF__nn_E_OBF__qq, axiom, ~ (e_OBF__nn = e_OBF__qq)).

tff(e_OBF__nn_E_OBF__rr, axiom, ~ (e_OBF__nn = e_OBF__rr)).

tff(e_OBF__nn_E_OBF__ss, axiom, ~ (e_OBF__nn = e_OBF__ss)).

tff(e_OBF__oo_E_OBF__pp, axiom, ~ (e_OBF__oo = e_OBF__pp)).

tff(e_OBF__oo_E_OBF__qq, axiom, ~ (e_OBF__oo = e_OBF__qq)).

tff(e_OBF__oo_E_OBF__rr, axiom, ~ (e_OBF__oo = e_OBF__rr)).

tff(e_OBF__oo_E_OBF__ss, axiom, ~ (e_OBF__oo = e_OBF__ss)).

tff(e_OBF__pp_E_OBF__qq, axiom, ~ (e_OBF__pp = e_OBF__qq)).

tff(e_OBF__pp_E_OBF__rr, axiom, ~ (e_OBF__pp = e_OBF__rr)).

tff(e_OBF__pp_E_OBF__ss, axiom, ~ (e_OBF__pp = e_OBF__ss)).

tff(e_OBF__qq_E_OBF__rr, axiom, ~ (e_OBF__qq = e_OBF__rr)).

tff(e_OBF__qq_E_OBF__ss, axiom, ~ (e_OBF__qq = e_OBF__ss)).

tff(e_OBF__rr_E_OBF__ss, axiom, ~ (e_OBF__rr = e_OBF__ss)).

tff(enum_OBF__ii_inversion, axiom, ![U:enum_OBF__ii]:
  ((((((((((U = e_OBF__jj) | (U = e_OBF__kk)) | (U = e_OBF__ll))
  | (U = e_OBF__mm)) | (U = e_OBF__nn)) | (U = e_OBF__oo)) | (U = e_OBF__pp))
  | (U = e_OBF__qq)) | (U = e_OBF__rr)) | (U = e_OBF__ss))).

tff(set_enum_OBF__ii, type, set_enum_OBF__ii: set(enum_OBF__ii)).

tff(set_enum_OBF__ii_axiom, axiom, ![X:enum_OBF__ii]: mem(enum_OBF__ii, X,
  set_enum_OBF__ii)).

tff(f1, type, f1: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f1_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f1(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb)
  <=> ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem(set($int), V_OBF__kkcc, power($int, V_OBF__cccc)))
  & mem(set($int), V_OBF__jjcc, power($int, V_OBF__cccc)))
  & mem(set($int), V_OBF__hhcc, power($int, V_OBF__cccc)))
  & mem(set($int), V_OBF__ffcc, power($int, V_OBF__cccc)))
  & mem(set($int), V_OBF__eecc, power($int, V_OBF__cccc)))
  & mem(set($int), V_OBF__ddcc, power($int, V_OBF__cccc)))
  & mem(set($int), V_OBF__zzbb, power($int, V_OBF__cccc)))
  & mem($int, V_OBF__xxbb, V_OBF__cccc)) & infix_eqeq($int, V_OBF__mmbb,
  union($int, union($int, union($int, union($int, union($int, union($int, union($int, V_OBF__kkcc,
  V_OBF__jjcc), V_OBF__hhcc), V_OBF__ffcc), V_OBF__eecc), V_OBF__ddcc),
  V_OBF__zzbb), singleton($int, V_OBF__xxbb)))) & mem(set($int), V_OBF__jjcc,
  power($int, diff($int, V_OBF__mmbb, V_OBF__kkcc))))
  & mem(set($int), V_OBF__hhcc, power($int, diff($int, V_OBF__mmbb,
  union($int, V_OBF__kkcc, V_OBF__jjcc))))) & mem(set($int), V_OBF__ffcc,
  power($int, diff($int, V_OBF__mmbb, union($int, union($int, V_OBF__kkcc,
  V_OBF__jjcc), V_OBF__hhcc))))) & mem(set($int), V_OBF__eecc,
  power($int, diff($int, V_OBF__mmbb,
  union($int, union($int, union($int, V_OBF__kkcc, V_OBF__jjcc),
  V_OBF__hhcc), V_OBF__ffcc))))) & mem(set($int), V_OBF__ddcc,
  power($int, diff($int, V_OBF__mmbb,
  union($int, union($int, union($int, union($int, V_OBF__kkcc, V_OBF__jjcc),
  V_OBF__hhcc), V_OBF__ffcc), V_OBF__eecc))))) & mem(set($int), V_OBF__zzbb,
  power($int, diff($int, V_OBF__mmbb,
  union($int, union($int, union($int, union($int, union($int, V_OBF__kkcc,
  V_OBF__jjcc), V_OBF__hhcc), V_OBF__ffcc), V_OBF__eecc), V_OBF__ddcc)))))
  & mem($int, V_OBF__xxbb, V_OBF__mmbb)) & ~ mem($int, V_OBF__xxbb,
  V_OBF__kkcc)) & ~ mem($int, V_OBF__xxbb, V_OBF__jjcc)) & ~
  mem($int, V_OBF__xxbb, V_OBF__hhcc)) & ~ mem($int, V_OBF__xxbb,
  V_OBF__ffcc)) & ~ mem($int, V_OBF__xxbb, V_OBF__eecc)) & ~
  mem($int, V_OBF__xxbb, V_OBF__ddcc)) & ~ mem($int, V_OBF__xxbb,
  V_OBF__zzbb)) & $true) & mem(set(tuple2($int, $int)), V_OBF__rrcc,
  relation($int, $int, V_OBF__cccc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__wwcc, relation($int,
  $int, V_OBF__cccc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__iiff, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__jjff, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, bool)), V_OBF__kkff, relation($int,
  bool, V_OBF__bbcc, b_bool))) & mem(set(tuple2($int, $int)), V_OBF__wwcc,
  power(tuple2($int, $int), V_OBF__rrcc)))
  & infix_eqeq(tuple2($int, $int), V_OBF__llff,
  inter(tuple2($int, $int), semicolon($int, $int, $int, V_OBF__iiff,
  V_OBF__rrcc), semicolon($int, $int, $int, V_OBF__jjff, inverse($int,
  $int, V_OBF__rrcc))))) & infix_eqeq(tuple2($int, $int), V_OBF__mmff,
  inter(tuple2($int, $int), semicolon($int, $int, $int, V_OBF__iiff,
  V_OBF__wwcc), semicolon($int, $int, $int, V_OBF__jjff, inverse($int,
  $int, V_OBF__rrcc))))) & infix_eqeq($int, V_OBF__nnff, image(bool,
  $int, inverse($int, bool, V_OBF__kkff), singleton(bool, true))))
  & mem(set(tuple2($int, $int)), V_OBF__iiff, infix_plmngt($int,
  $int, V_OBF__bbcc, V_OBF__cccc))) & infix_eqeq($int, dom($int,
  $int, V_OBF__iiff), V_OBF__bbcc))
  & mem(set(tuple2($int, $int)), V_OBF__jjff, infix_plmngt($int,
  $int, V_OBF__bbcc, V_OBF__cccc))) & infix_eqeq($int, dom($int,
  $int, V_OBF__jjff), V_OBF__bbcc))
  & mem(set(tuple2($int, bool)), V_OBF__kkff, infix_plmngt($int,
  bool, V_OBF__bbcc, b_bool))) & infix_eqeq($int, dom($int,
  bool, V_OBF__kkff), V_OBF__bbcc)) & $true) & $true)
  & mem(set(tuple2($int, $int)), V_OBF__llff, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__mmff, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__ooff, relation($int,
  $int, V_OBF__bbcc, V_OBF__bbbb)))
  & mem(set(tuple2($int, $int)), V_OBF__ppff, relation($int,
  $int, V_OBF__bbcc, V_OBF__dddd))) & mem(set($int), V_OBF__nnff,
  power($int, V_OBF__bbcc))) & infix_eqeq(tuple2($int, $int), V_OBF__qqff,
  image($int, tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__nnff, direct_product($int, $int,
  tuple2($int, $int), V_OBF__ppff, direct_product($int, $int,
  $int, V_OBF__llff, V_OBF__ooff)))), singleton($int, V_OBF__ggbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__rrff, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__nnff, direct_product($int, $int,
  tuple2($int, $int), V_OBF__ppff, direct_product($int, $int,
  $int, V_OBF__llff, V_OBF__ooff)))), singleton($int, V_OBF__hhbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__hhee, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__nnff, direct_product($int, $int,
  tuple2($int, $int), V_OBF__ppff, direct_product($int, $int,
  $int, V_OBF__llff, V_OBF__ooff)))), singleton($int, V_OBF__ffbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__ggee, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__nnff, direct_product($int, $int,
  tuple2($int, $int), V_OBF__ppff, direct_product($int, $int,
  $int, V_OBF__mmff, V_OBF__ooff)))), singleton($int, V_OBF__ffbb))))
  & mem(set(tuple2($int, $int)), V_OBF__mmff,
  power(tuple2($int, $int), V_OBF__llff)))
  & mem(set(tuple2($int, $int)), V_OBF__ooff, infix_plmngt($int,
  $int, V_OBF__bbcc, V_OBF__bbbb))) & infix_eqeq($int, dom($int,
  $int, V_OBF__ooff), V_OBF__bbcc)) & mem(set($int), ran($int,
  $int, V_OBF__ppff),
  power($int, union($int, union($int, singleton($int, V_OBF__ggbb),
  singleton($int, V_OBF__hhbb)), singleton($int, V_OBF__ffbb)))))
  & mem(set($int), V_OBF__bbcc, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__bbcc, empty($int)))
  & mem(set(tuple2($int, $int)), V_OBF__hhee, relation($int,
  $int, V_OBF__cccc, V_OBF__bbbb)))
  & mem(set(tuple2($int, $int)), V_OBF__ggee, relation($int,
  $int, V_OBF__cccc, V_OBF__bbbb))) & mem(set($int), V_OBF__iiee,
  power($int, V_OBF__bbbb))) & infix_eqeq(tuple2($int, $int), V_OBF__ssff,
  times($int, $int, diff($int, dom($int, $int, V_OBF__hhee), dom($int,
  tuple2($int, $int), range_substraction($int,
  tuple2($int, $int), direct_product($int, $int, $int, V_OBF__hhee,
  V_OBF__hhee), id($int, V_OBF__bbbb)))), V_OBF__bbbb)))
  & mem(set(tuple2($int, $int)), V_OBF__ggee,
  power(tuple2($int, $int), V_OBF__hhee))) & mem($int, V_OBF__uucc,
  V_OBF__bbbb)) & mem(set(tuple2($int, $int)), V_OBF__qqff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__rrff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & ~ (V_OBF__uucc = V_OBF__ssbb))
  & infix_eqeq(tuple2($int, $int), V_OBF__ttff,
  union(tuple2($int, $int), V_OBF__qqff, semicolon($int, $int,
  $int, V_OBF__qqff, times($int, $int, singleton($int, V_OBF__uucc),
  V_OBF__bbbb))))) & infix_eqeq(tuple2($int, $int), V_OBF__uuff,
  union(tuple2($int, $int), V_OBF__rrff, semicolon($int, $int,
  $int, V_OBF__rrff, times($int, $int, singleton($int, V_OBF__uucc),
  V_OBF__bbbb))))) & mem($int, V_OBF__llbb, V_OBF__ppdd))
  & mem($int, V_OBF__ssbb, V_OBF__bbbb)) & mem(set($int), V_OBF__uu,
  power($int, V_OBF__cccc))) & mem(set($int), V_OBF__iibb,
  power($int, V_OBF__cccc))) & mem(set($int), V_OBF__mmbb,
  power($int, V_OBF__cccc))) & mem(set($int), V_OBF__nnbb,
  power($int, V_OBF__cccc))) & mem($int, V_OBF__oobb, V_OBF__cccc))
  & mem($int, V_OBF__ppbb, V_OBF__cccc)) & mem($int, V_OBF__qqbb,
  V_OBF__cccc)) & mem($int, V_OBF__rrbb, V_OBF__cccc))
  & mem(set(tuple2($int, $int)), V_OBF__ttff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__uuff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__ssff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set($int), V_OBF__vvff, power($int, V_OBF__bbbb)))
  & mem(set($int), V_OBF__iibb, power($int, V_OBF__uu)))
  & mem(set($int), V_OBF__mmbb, power($int, diff($int, V_OBF__cccc,
  V_OBF__uu)))) & mem(set($int), V_OBF__nnbb,
  power($int, diff($int, V_OBF__cccc, union($int, V_OBF__uu, V_OBF__mmbb)))))
  & ~ mem($int, V_OBF__oobb, V_OBF__uu)) & ~ mem($int, V_OBF__oobb,
  V_OBF__mmbb)) & ~ mem($int, V_OBF__oobb, V_OBF__nnbb)) & ~
  (V_OBF__oobb = V_OBF__ppbb)) & ~ (V_OBF__oobb = V_OBF__qqbb)) & ~
  (V_OBF__oobb = V_OBF__rrbb)) & ~ mem($int, V_OBF__ppbb, V_OBF__uu)) & ~
  mem($int, V_OBF__ppbb, V_OBF__mmbb)) & ~ mem($int, V_OBF__ppbb,
  V_OBF__nnbb)) & ~ (V_OBF__ppbb = V_OBF__oobb)) & ~
  (V_OBF__ppbb = V_OBF__qqbb)) & ~ (V_OBF__ppbb = V_OBF__rrbb)) & ~
  mem($int, V_OBF__qqbb, V_OBF__uu)) & ~ mem($int, V_OBF__qqbb, V_OBF__mmbb))
  & ~ mem($int, V_OBF__qqbb, V_OBF__nnbb)) & ~ (V_OBF__qqbb = V_OBF__oobb))
  & ~ (V_OBF__qqbb = V_OBF__ppbb)) & ~ (V_OBF__qqbb = V_OBF__rrbb)) & ~
  mem($int, V_OBF__rrbb, V_OBF__uu)) & ~ mem($int, V_OBF__rrbb, V_OBF__mmbb))
  & ~ mem($int, V_OBF__rrbb, V_OBF__nnbb)) & ~ (V_OBF__rrbb = V_OBF__oobb))
  & ~ (V_OBF__rrbb = V_OBF__ppbb)) & ~ (V_OBF__rrbb = V_OBF__qqbb))
  & infix_eqeq($int, V_OBF__cccc,
  union($int, union($int, union($int, V_OBF__uu, V_OBF__mmbb), V_OBF__nnbb),
  union($int, union($int, union($int, singleton($int, V_OBF__oobb),
  singleton($int, V_OBF__ppbb)), singleton($int, V_OBF__qqbb)),
  singleton($int, V_OBF__rrbb)))))
  & infix_eqeq(tuple2($int, $int), V_OBF__wwff,
  union(tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int,
                                                            $int), union(
  tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int, $int), domain_restriction($int,
  $int, V_OBF__uu, V_OBF__ttff), times($int, $int, V_OBF__nnbb,
  V_OBF__vvff)), times($int, $int, union($int, singleton($int, V_OBF__oobb),
  singleton($int, V_OBF__ppbb)), V_OBF__vvff)), times($int,
  $int, V_OBF__mmbb, singleton($int, V_OBF__ssbb))), times($int,
  $int, V_OBF__iibb, V_OBF__bbbb)), times($int,
  $int, singleton($int, V_OBF__qqbb), V_OBF__bbbb)),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__rrbb,
  V_OBF__ssbb)))))
  & infix_eqeq(tuple2(tuple2($int, $int), $int), V_OBF__xxff,
  union(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, union(tuple2($int, $int), union(tuple2($int, $int), domain_restriction($int,
  $int, V_OBF__uu, V_OBF__uuff), times($int, $int, V_OBF__nnbb,
  V_OBF__vvff)), singleton(tuple2($int, $int), tuple21($int,
  $int, V_OBF__rrbb, V_OBF__ssbb))), V_OBF__ppdd), times(tuple2($int, $int),
  $int, times($int, $int, union($int, singleton($int, V_OBF__oobb),
  singleton($int, V_OBF__ppbb)), V_OBF__vvff),
  singleton($int, V_OBF__llbb)))))
  & infix_eqeq(tuple2($int, $int), V_OBF__yyff, domain_restriction($int,
  $int, V_OBF__uu, V_OBF__ssff))) & mem($int, V_OBF__wwdd, integer))
  & infix_eqeq(tuple2($int, $int), V_OBF__zzff, times($int,
  $int, V_OBF__cccc, V_OBF__bbbb)))
  & infix_eqeq(tuple2($int, $int), V_OBF__aagg, times($int,
  $int, V_OBF__cccc, V_OBF__bbbb))) & $lesseq(1,V_OBF__wwdd))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbgg,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccgg,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddgg,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eegg,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aaee,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__bbgg,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 0),
  union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__bb),
  singleton(enum_OBF__aa, e_OBF__ff)), singleton(enum_OBF__aa, e_OBF__gg)),
  singleton(enum_OBF__aa, e_OBF__ee)), singleton(enum_OBF__aa, e_OBF__cc))),
  singleton($int, 0))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__ccgg,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 0),
  union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__hh),
  singleton(enum_OBF__aa, e_OBF__dd))), singleton($int, 1))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__ddgg,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 1), singleton(enum_OBF__aa, e_OBF__cc)),
  singleton($int, 0))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__eegg,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 1),
  union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__bb),
  singleton(enum_OBF__aa, e_OBF__ff)), singleton(enum_OBF__aa, e_OBF__gg)),
  singleton(enum_OBF__aa, e_OBF__ee)), singleton(enum_OBF__aa, e_OBF__hh)),
  singleton(enum_OBF__aa, e_OBF__dd))), singleton($int, 1))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__aaee,
  union(tuple2(tuple2($int, enum_OBF__aa), $int), union(tuple2(tuple2($int,
                                                               enum_OBF__aa),
                                                        $int), union(
  tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__bbgg, V_OBF__ccgg),
  V_OBF__ddgg), V_OBF__eegg))) & $true) & $true)
  & mem(set(tuple2($int, $int)), V_OBF__wwff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__xxff,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__cccc, V_OBF__bbbb), V_OBF__ppdd))))
  & mem(set(tuple2($int, $int)), V_OBF__yyff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__zzff,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__aagg,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__ffgg,
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
  $int, times(tuple2($int, $int), $int, V_OBF__wwff, V_OBF__ppdd),
  singleton($int, V_OBF__ggbb)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__xxff, singleton($int, V_OBF__hhbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__yyff, V_OBF__ppdd), singleton($int, V_OBF__ffbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__zzff, V_OBF__ppdd), singleton($int, V_OBF__ccee))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__aagg, V_OBF__ppdd), singleton($int, V_OBF__ddee))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__cccc, V_OBF__bbbb), V_OBF__ppdd),
  singleton($int, V_OBF__eeee)))))
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffgg,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__cccc,
  V_OBF__bbbb), V_OBF__ppdd), V_OBF__dddd)))) & mem($int, V_OBF__ggbb,
  V_OBF__dddd)) & mem($int, V_OBF__hhbb, V_OBF__dddd))
  & mem($int, V_OBF__ffbb, V_OBF__dddd)) & mem($int, V_OBF__ccee,
  V_OBF__dddd)) & mem($int, V_OBF__ddee, V_OBF__dddd))
  & mem($int, V_OBF__eeee, V_OBF__dddd)) & ~ (V_OBF__ggbb = V_OBF__hhbb)) & ~
  (V_OBF__ggbb = V_OBF__ffbb)) & ~ (V_OBF__ggbb = V_OBF__ccee)) & ~
  (V_OBF__ggbb = V_OBF__ddee)) & ~ (V_OBF__ggbb = V_OBF__eeee)) & ~
  (V_OBF__hhbb = V_OBF__ggbb)) & ~ (V_OBF__hhbb = V_OBF__ffbb)) & ~
  (V_OBF__hhbb = V_OBF__ccee)) & ~ (V_OBF__hhbb = V_OBF__ddee)) & ~
  (V_OBF__hhbb = V_OBF__eeee)) & ~ (V_OBF__ffbb = V_OBF__ggbb)) & ~
  (V_OBF__ffbb = V_OBF__hhbb)) & ~ (V_OBF__ffbb = V_OBF__ccee)) & ~
  (V_OBF__ffbb = V_OBF__ddee)) & ~ (V_OBF__ffbb = V_OBF__eeee)) & ~
  (V_OBF__ccee = V_OBF__ggbb)) & ~ (V_OBF__ccee = V_OBF__hhbb)) & ~
  (V_OBF__ccee = V_OBF__ffbb)) & ~ (V_OBF__ccee = V_OBF__ddee)) & ~
  (V_OBF__ccee = V_OBF__eeee)) & ~ (V_OBF__ddee = V_OBF__ggbb)) & ~
  (V_OBF__ddee = V_OBF__hhbb)) & ~ (V_OBF__ddee = V_OBF__ffbb)) & ~
  (V_OBF__ddee = V_OBF__ccee)) & ~ (V_OBF__ddee = V_OBF__eeee)) & ~
  (V_OBF__eeee = V_OBF__ggbb)) & ~ (V_OBF__eeee = V_OBF__hhbb)) & ~
  (V_OBF__eeee = V_OBF__ffbb)) & ~ (V_OBF__eeee = V_OBF__ccee)) & ~
  (V_OBF__eeee = V_OBF__ddee)) & mem(set($int), V_OBF__cccc,
  finite_subsets($int, integer))) & ~ infix_eqeq($int, V_OBF__cccc,
  empty($int))) & mem(set($int), V_OBF__bbbb, finite_subsets($int, integer)))
  & ~ infix_eqeq($int, V_OBF__bbbb, empty($int)))
  & mem(set($int), V_OBF__ppdd, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__ppdd, empty($int))) & mem(set($int), V_OBF__dddd,
  finite_subsets($int, integer))) & ~ infix_eqeq($int, V_OBF__dddd,
  empty($int))))).

tff(f2, type, f2: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f2_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f2(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb)
  <=> ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem(set(tuple2($int, $int)), V_OBF__qqcc, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__sscc, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, bool)), V_OBF__ppcc, relation($int,
  bool, V_OBF__bbcc, b_bool))) & infix_eqeq(tuple2($int, $int), V_OBF__aadd,
  inter(tuple2($int, $int), semicolon($int, $int, $int, V_OBF__qqcc,
  V_OBF__rrcc), semicolon($int, $int, $int, V_OBF__sscc, inverse($int,
  $int, V_OBF__rrcc))))) & infix_eqeq(tuple2($int, $int), V_OBF__bbdd,
  inter(tuple2($int, $int), semicolon($int, $int, $int, V_OBF__qqcc,
  V_OBF__wwcc), semicolon($int, $int, $int, V_OBF__sscc, inverse($int,
  $int, V_OBF__rrcc))))) & infix_eqeq($int, V_OBF__ccdd, image(bool,
  $int, inverse($int, bool, V_OBF__ppcc), singleton(bool, true))))
  & mem(set(tuple2($int, $int)), V_OBF__qqcc, infix_plmngt($int,
  $int, V_OBF__bbcc, V_OBF__cccc))) & infix_eqeq($int, dom($int,
  $int, V_OBF__qqcc), V_OBF__bbcc))
  & mem(set(tuple2($int, $int)), V_OBF__sscc, infix_plmngt($int,
  $int, V_OBF__bbcc, V_OBF__cccc))) & infix_eqeq($int, dom($int,
  $int, V_OBF__sscc), V_OBF__bbcc))
  & mem(set(tuple2($int, bool)), V_OBF__ppcc, infix_plmngt($int,
  bool, V_OBF__bbcc, b_bool))) & infix_eqeq($int, dom($int,
  bool, V_OBF__ppcc), V_OBF__bbcc)) & mem(set(enum_OBF__ii), V_OBF__uubb,
  power(enum_OBF__ii, set_enum_OBF__ii)))
  & mem(set(tuple2($int, $int)), V_OBF__aadd, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__bbdd, relation($int,
  $int, V_OBF__bbcc, V_OBF__cccc)))
  & mem(set(tuple2($int, $int)), V_OBF__ttcc, relation($int,
  $int, V_OBF__bbcc, V_OBF__bbbb)))
  & mem(set(tuple2($int, $int)), V_OBF__iicc, relation($int,
  $int, V_OBF__bbcc, V_OBF__dddd))) & mem(set($int), V_OBF__ccdd,
  power($int, V_OBF__bbcc))) & mem(set($int), V_OBF__jjbb,
  power($int, V_OBF__bbcc))) & mem(set($int), V_OBF__eedd,
  power($int, V_OBF__bbcc))) & mem(set($int), V_OBF__ww,
  power($int, V_OBF__bbbb))) & mem(set($int), V_OBF__zz,
  power($int, V_OBF__bbcc))) & mem(set($int), V_OBF__ffdd,
  power($int, V_OBF__bbcc))) & infix_eqeq(tuple2($int, $int), V_OBF__ggdd,
  image($int, tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccdd, direct_product($int, $int,
  tuple2($int, $int), V_OBF__iicc, direct_product($int, $int,
  $int, V_OBF__aadd, V_OBF__ttcc)))), singleton($int, V_OBF__ggbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__hhdd, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccdd, direct_product($int, $int,
  tuple2($int, $int), V_OBF__iicc, direct_product($int, $int,
  $int, V_OBF__aadd, V_OBF__ttcc)))), singleton($int, V_OBF__hhbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__iidd, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccdd, direct_product($int, $int,
  tuple2($int, $int), V_OBF__iicc, direct_product($int, $int,
  $int, V_OBF__aadd, V_OBF__ttcc)))), singleton($int, V_OBF__ffbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__jjdd, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccdd, direct_product($int, $int,
  tuple2($int, $int), V_OBF__iicc, direct_product($int, $int,
  $int, V_OBF__bbdd, V_OBF__ttcc)))), singleton($int, V_OBF__ffbb))))
  & mem(set(tuple2($int, $int)), V_OBF__bbdd,
  power(tuple2($int, $int), V_OBF__aadd)))
  & mem(set(tuple2($int, $int)), V_OBF__ttcc, infix_plmngt($int,
  $int, V_OBF__bbcc, V_OBF__bbbb))) & infix_eqeq($int, dom($int,
  $int, V_OBF__ttcc), V_OBF__bbcc)) & mem(set($int), ran($int,
  $int, V_OBF__iicc),
  power($int, union($int, union($int, singleton($int, V_OBF__ggbb),
  singleton($int, V_OBF__hhbb)), singleton($int, V_OBF__ffbb)))))
  & ((V_OBF__ddbb = 2) => infix_eqeq($int, V_OBF__jjbb,
  inter($int, V_OBF__ccdd, image($int, $int, inverse($int,
  $int, V_OBF__aadd), singleton($int, V_OBF__tt)))))) & ((V_OBF__ddbb = 2)
  => infix_eqeq($int, V_OBF__eedd, inter($int, inter($int, V_OBF__ccdd,
  image($int, $int, inverse($int, $int, V_OBF__aadd),
  singleton($int, V_OBF__tt))), image($int, $int, inverse($int,
  $int, V_OBF__iicc), singleton($int, V_OBF__eebb)))))) & ((V_OBF__ddbb = 2)
  => infix_eqeq($int, V_OBF__ww, image($int, $int, V_OBF__ttcc,
  V_OBF__eedd)))) & ((V_OBF__ddbb = 2) => infix_eqeq($int, V_OBF__zz,
  inter($int, inter($int, V_OBF__ccdd, image($int, $int, inverse($int,
  $int, V_OBF__bbdd), singleton($int, V_OBF__tt))), image($int,
  $int, inverse($int, $int, V_OBF__iicc), singleton($int, V_OBF__eebb))))))
  & ((V_OBF__ddbb = 2) => infix_eqeq($int, V_OBF__ffdd,
  inter($int, inter($int, inter($int, V_OBF__ccdd, image($int,
  $int, inverse($int, $int, V_OBF__aadd), singleton($int, V_OBF__tt))),
  image($int, $int, inverse($int, $int, V_OBF__iicc),
  singleton($int, V_OBF__eebb))), image($int, $int, inverse($int,
  $int, V_OBF__ttcc), union($int, singleton($int, V_OBF__vv),
  singleton($int, V_OBF__uucc)))))))
  & mem(set(tuple2($int, $int)), V_OBF__iidd, relation($int,
  $int, V_OBF__cccc, V_OBF__bbbb)))
  & mem(set(tuple2($int, $int)), V_OBF__jjdd, relation($int,
  $int, V_OBF__cccc, V_OBF__bbbb))) & mem(set($int), V_OBF__yy,
  power($int, V_OBF__bbbb))) & infix_eqeq(tuple2($int, $int), V_OBF__kkdd,
  times($int, $int, diff($int, dom($int,
  $int, union(tuple2($int, $int), V_OBF__jjdd, range_substraction($int,
  $int, V_OBF__iidd, image($int, $int, times($int, $int, singleton($int, 0),
  diff($int, V_OBF__yy, singleton($int, V_OBF__vv))),
  singleton($int, V_OBF__xx))))), dom($int,
  tuple2($int, $int), range_substraction($int,
  tuple2($int, $int), direct_product($int, $int, $int, V_OBF__iidd,
  V_OBF__iidd), id($int, V_OBF__bbbb)))), V_OBF__bbbb)))
  & mem(set(tuple2($int, $int)), V_OBF__jjdd,
  power(tuple2($int, $int), V_OBF__iidd)))
  & mem(set(tuple2($int, $int)), V_OBF__ggdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__hhdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & infix_eqeq(tuple2($int, $int), V_OBF__lldd,
  union(tuple2($int, $int), V_OBF__ggdd, semicolon($int, $int,
  $int, V_OBF__ggdd, times($int, $int, singleton($int, V_OBF__uucc),
  V_OBF__bbbb))))) & infix_eqeq(tuple2($int, $int), V_OBF__mmdd,
  union(tuple2($int, $int), V_OBF__hhdd, semicolon($int, $int,
  $int, V_OBF__hhdd, times($int, $int, singleton($int, V_OBF__uucc),
  V_OBF__bbbb))))) & mem(set(tuple2($int, $int)), V_OBF__lldd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__mmdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__kkdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & $true) & mem(set($int), V_OBF__ttbb, power($int, V_OBF__bbbb)))
  & infix_eqeq(tuple2($int, $int), V_OBF__nndd,
  union(tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int,
                                                            $int), union(
  tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int, $int), domain_restriction($int,
  $int, V_OBF__uu, V_OBF__lldd), times($int, $int, V_OBF__nnbb,
  V_OBF__ttbb)), times($int, $int, union($int, singleton($int, V_OBF__oobb),
  singleton($int, V_OBF__ppbb)), V_OBF__ttbb)), times($int,
  $int, V_OBF__mmbb, singleton($int, V_OBF__ssbb))), dom(tuple2($int, $int),
  $int, range_restriction(tuple2($int, $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__iibb, V_OBF__bbbb), singleton($int, 1)),
  singleton($int, V_OBF__xx)))), times($int,
  $int, singleton($int, V_OBF__qqbb), V_OBF__bbbb)),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__rrbb,
  V_OBF__ssbb)))))
  & infix_eqeq(tuple2(tuple2($int, $int), $int), V_OBF__oodd,
  union(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, union(tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int,
                                                                  $int), domain_restriction($int,
  $int, V_OBF__uu, V_OBF__mmdd), times($int, $int, V_OBF__nnbb,
  V_OBF__ttbb)), dom(tuple2($int, $int),
  bool, range_restriction(tuple2($int, $int), bool, times(tuple2($int, $int),
  bool, times($int, $int, V_OBF__mmbb, singleton($int, V_OBF__ssbb)),
  singleton(bool, false)), singleton(bool, V_OBF__yybb)))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__rrbb,
  V_OBF__ssbb))), V_OBF__ppdd), times(tuple2($int, $int), $int, times($int,
  $int, union($int, singleton($int, V_OBF__oobb),
  singleton($int, V_OBF__ppbb)), V_OBF__ttbb),
  singleton($int, V_OBF__llbb)))))
  & infix_eqeq(tuple2($int, $int), V_OBF__qqdd, domain_restriction($int,
  $int, V_OBF__uu, V_OBF__kkdd))) & mem($int, V_OBF__rrdd, V_OBF__bbbb))
  & mem($int, V_OBF__ssdd, integer))
  & mem(set(tuple2($int, $int)), V_OBF__ttdd, relation($int, $int, integer,
  V_OBF__bbbb))) & mem(set(tuple2($int, $int)), V_OBF__uudd, relation($int,
  $int, integer, V_OBF__bbbb))) & infix_eqeq(tuple2($int, $int), V_OBF__vvdd,
  dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__wwdd, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__ssdd,
  V_OBF__xx)))))) & infix_eqeq(tuple2($int, $int), V_OBF__xxdd,
  dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb),
  singleton(tuple2($int, $int), tuple21($int, $int, 0, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__ssdd,
  V_OBF__xx)))))) & mem($int, V_OBF__ssdd, mk(0, V_OBF__wwdd)))
  & mem(set(tuple2($int, $int)), V_OBF__ttdd, infix_plmngt($int, $int, mk(1,
  V_OBF__wwdd), V_OBF__bbbb))) & infix_eqeq($int, dom($int,
  $int, V_OBF__ttdd), mk(1, V_OBF__wwdd)))
  & mem(set(tuple2($int, $int)), V_OBF__uudd, infix_plmngt($int, $int, mk(1,
  V_OBF__wwdd), V_OBF__bbbb))) & infix_eqeq($int, dom($int,
  $int, V_OBF__uudd), mk(1, V_OBF__wwdd))) & mem($int, V_OBF__yydd, integer))
  & $true) & mem($int, V_OBF__xx, integer))
  & mem(tuple2(tuple2($int, enum_OBF__aa), $int), tuple21($int,
  tuple2($int, enum_OBF__aa), tuple21(enum_OBF__aa, $int, V_OBF__yydd,
  V_OBF__zzdd), V_OBF__xx), V_OBF__aaee))
  & mem(set(tuple2($int, $int)), V_OBF__nndd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__oodd,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__cccc, V_OBF__bbbb), V_OBF__ppdd))))
  & mem(set(tuple2($int, $int)), V_OBF__qqdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__vvdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & mem(set(tuple2($int, $int)), V_OBF__xxdd,
  power(tuple2($int, $int), times($int, $int, V_OBF__cccc, V_OBF__bbbb))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__bbee,
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
  $int, times(tuple2($int, $int), $int, V_OBF__nndd, V_OBF__ppdd),
  singleton($int, V_OBF__ggbb)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__oodd, singleton($int, V_OBF__hhbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__qqdd, V_OBF__ppdd), singleton($int, V_OBF__ffbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__vvdd, V_OBF__ppdd), singleton($int, V_OBF__ccee))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__xxdd, V_OBF__ppdd), singleton($int, V_OBF__ddee))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__cccc, V_OBF__bbbb), V_OBF__ppdd),
  singleton($int, V_OBF__eeee))))) & mem($int, V_OBF__ddbb, integer))
  & mem($int, V_OBF__tt, V_OBF__cccc)) & mem($int, V_OBF__vv, V_OBF__bbbb))
  & mem($int, V_OBF__kkbb, V_OBF__ppdd)) & mem($int, V_OBF__eebb,
  V_OBF__dddd)) & $true)
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbee,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__cccc,
  V_OBF__bbbb), V_OBF__ppdd), V_OBF__dddd)))) & $true) & ((V_OBF__ddbb = 2)
  => infix_eqeq($int, V_OBF__eedd, inter($int, V_OBF__jjbb, image($int,
  $int, inverse($int, $int, V_OBF__iicc), singleton($int, V_OBF__eebb))))))
  & (((V_OBF__ddbb = 2) & (V_OBF__eebb = V_OBF__ffbb))
  => infix_eqeq($int, image($int, $int, V_OBF__ttcc, V_OBF__zz), image($int,
  $int, V_OBF__jjdd, singleton($int, V_OBF__tt))))) & (((V_OBF__ddbb = 2)
  & (V_OBF__eebb = V_OBF__ffbb)) => infix_eqeq($int, V_OBF__ww, image($int,
  $int, V_OBF__iidd, singleton($int, V_OBF__tt)))))
  & infix_eqeq(tuple2($int, $int), union(tuple2($int, $int), V_OBF__jjdd,
  range_substraction($int, $int, V_OBF__iidd, image($int, $int, times($int,
  $int, singleton($int, 0), diff($int, V_OBF__yy,
  singleton($int, V_OBF__vv))), singleton($int, 1)))), V_OBF__iidd))
  & infix_eqeq(tuple2($int, $int), union(tuple2($int, $int), V_OBF__jjdd,
  range_substraction($int, $int, V_OBF__iidd, image($int, $int, times($int,
  $int, singleton($int, 0), diff($int, V_OBF__yy,
  singleton($int, V_OBF__vv))), singleton($int, 0)))),
  union(tuple2($int, $int), V_OBF__jjdd, range_substraction($int,
  $int, V_OBF__iidd, diff($int, V_OBF__yy, singleton($int, V_OBF__vv))))))
  & infix_eqeq(tuple2($int, $int), union(tuple2($int, $int), V_OBF__ggee,
  range_substraction($int, $int, V_OBF__hhee, image($int, $int, times($int,
  $int, singleton($int, 0), diff($int, V_OBF__iiee,
  singleton($int, V_OBF__ssbb))), singleton($int, 1)))), V_OBF__hhee))
  & mem($int, V_OBF__xx, union($int, singleton($int, 0),
  singleton($int, 1))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aaee,
  infix_plmngt(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, union($int, singleton($int, 0), singleton($int, 1)),
  set_enum_OBF__aa), union($int, singleton($int, 0), singleton($int, 1)))))
  & infix_eqeq(tuple2($int, enum_OBF__aa), dom(tuple2($int, enum_OBF__aa),
  $int, V_OBF__aaee), times($int,
  enum_OBF__aa, union($int, singleton($int, 0), singleton($int, 1)),
  set_enum_OBF__aa))) & $true) & (V_OBF__jjee = V_OBF__ddbb))
  & (V_OBF__kkee = V_OBF__tt)) & (V_OBF__llee = V_OBF__vv))
  & (V_OBF__mmee = V_OBF__kkbb)) & (V_OBF__nnee = V_OBF__eebb))
  & (V_OBF__ooee = V_OBF__ffee)) & (V_OBF__ppee = V_OBF__xx))
  & (V_OBF__qqee = V_OBF__rrdd)) & (V_OBF__rree = V_OBF__ssdd))
  & infix_eqeq(tuple2($int, $int), V_OBF__ssee, V_OBF__ttdd))
  & infix_eqeq(tuple2($int, $int), V_OBF__ttee, V_OBF__uudd))
  & (V_OBF__uuee = V_OBF__yybb)) & infix_eqeq($int, V_OBF__vvee,
  V_OBF__ttbb)) & infix_eqeq($int, V_OBF__wwee, V_OBF__yy))
  & infix_eqeq(tuple2($int, $int), V_OBF__xxee, V_OBF__ttcc))
  & infix_eqeq(tuple2($int, $int), V_OBF__yyee, V_OBF__iicc))
  & infix_eqeq($int, V_OBF__zzee, V_OBF__jjbb))
  & infix_eqeq($int, V_OBF__aaff, V_OBF__eedd))
  & infix_eqeq($int, V_OBF__bbff, V_OBF__ww)) & infix_eqeq($int, V_OBF__ccff,
  V_OBF__zz)) & infix_eqeq($int, V_OBF__ddff, V_OBF__ffdd))
  & infix_eqeq(enum_OBF__ii, V_OBF__eeff, V_OBF__uubb))
  & infix_eqeq(tuple2($int, $int), V_OBF__ffff, V_OBF__qqcc))
  & infix_eqeq(tuple2($int, $int), V_OBF__ggff, V_OBF__sscc))
  & infix_eqeq(tuple2($int, bool), V_OBF__hhff, V_OBF__ppcc)))).

tff(f3, type, f3: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f3_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f3(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb) <=> (((((($true & infix_eqeq($int, V_OBF__oocc,
  inter($int, V_OBF__yycc, image($int, $int, inverse($int,
  $int, V_OBF__ttcc), union($int, singleton($int, V_OBF__vv),
  singleton($int, V_OBF__uucc)))))) & (V_OBF__ddbb = 1))
  & infix_eqeq($int, V_OBF__zzcc, inter($int, inter($int, image(bool,
  $int, inverse($int, bool, V_OBF__ppcc), singleton(bool, true)), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__qqcc,
  V_OBF__rrcc)), singleton($int, V_OBF__tt))), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__sscc,
  inverse($int, $int, V_OBF__rrcc))), singleton($int, V_OBF__tt)))))
  & infix_eqeq($int, V_OBF__yycc, inter($int, V_OBF__zzcc, image($int,
  $int, inverse($int, $int, V_OBF__iicc), singleton($int, V_OBF__eebb)))))
  & infix_eqeq($int, V_OBF__xxcc, image($int, $int, V_OBF__ttcc,
  V_OBF__yycc))) & infix_eqeq($int, V_OBF__vvcc, inter($int, V_OBF__yycc,
  image($int, $int, inverse($int, $int, semicolon($int, $int,
  $int, V_OBF__qqcc, V_OBF__wwcc)), singleton($int, V_OBF__tt))))))).

tff(f5, type, f5: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f5_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f5(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq($int, V_OBF__yycc,
  inter($int, inter($int, inter($int, image(bool, $int, inverse($int,
  bool, V_OBF__ppcc), singleton(bool, true)), image($int, $int, inverse($int,
  $int, semicolon($int, $int, $int, V_OBF__qqcc, V_OBF__rrcc)),
  singleton($int, V_OBF__tt))), image($int, $int, inverse($int,
  $int, semicolon($int, $int, $int, V_OBF__sscc, inverse($int,
  $int, V_OBF__rrcc))), singleton($int, V_OBF__tt))), image($int,
  $int, inverse($int, $int, V_OBF__iicc), singleton($int, V_OBF__eebb)))))).

tff(f7, type, f7: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f7_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f7(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq($int, V_OBF__xxcc, image($int,
  $int, V_OBF__ttcc, inter($int, inter($int, inter($int, image(bool,
  $int, inverse($int, bool, V_OBF__ppcc), singleton(bool, true)), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__qqcc,
  V_OBF__rrcc)), singleton($int, V_OBF__tt))), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__sscc,
  inverse($int, $int, V_OBF__rrcc))), singleton($int, V_OBF__tt))),
  image($int, $int, inverse($int, $int, V_OBF__iicc),
  singleton($int, V_OBF__eebb))))))).

tff(f9, type, f9: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f9_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f9(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq($int, V_OBF__vvcc,
  inter($int, inter($int, inter($int, inter($int, image(bool,
  $int, inverse($int, bool, V_OBF__ppcc), singleton(bool, true)), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__qqcc,
  V_OBF__rrcc)), singleton($int, V_OBF__tt))), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__sscc,
  inverse($int, $int, V_OBF__rrcc))), singleton($int, V_OBF__tt))),
  image($int, $int, inverse($int, $int, V_OBF__iicc),
  singleton($int, V_OBF__eebb))), image($int, $int, inverse($int,
  $int, semicolon($int, $int, $int, V_OBF__qqcc, V_OBF__wwcc)),
  singleton($int, V_OBF__tt)))))).

tff(f11, type, f11: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f11_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f11(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> infix_eqeq($int, V_OBF__oocc,
  inter($int, inter($int, inter($int, inter($int, image(bool,
  $int, inverse($int, bool, V_OBF__ppcc), singleton(bool, true)), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__qqcc,
  V_OBF__rrcc)), singleton($int, V_OBF__tt))), image($int,
  $int, inverse($int, $int, semicolon($int, $int, $int, V_OBF__sscc,
  inverse($int, $int, V_OBF__rrcc))), singleton($int, V_OBF__tt))),
  image($int, $int, inverse($int, $int, V_OBF__iicc),
  singleton($int, V_OBF__eebb))), image($int, $int, inverse($int,
  $int, V_OBF__ttcc), union($int, singleton($int, V_OBF__vv),
  singleton($int, V_OBF__uucc))))))).

tff(f12, type, f12: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f12_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f12(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> (((((((((($true & mem($int, V_OBF__tt,
  V_OBF__kkcc)) & mem(set(tuple2($int, $int)), V_OBF__llcc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__bbbb)))
  & infix_eqeq($int, dom($int, $int, V_OBF__llcc), V_OBF__bbcc))
  & mem(set(tuple2($int, $int)), V_OBF__mmcc, relation($int,
  $int, V_OBF__bbcc, union($int, union($int, singleton($int, V_OBF__ggbb),
  singleton($int, V_OBF__hhbb)), singleton($int, V_OBF__ffbb)))))
  & mem(set(tuple2($int, bool)), V_OBF__nncc, infix_plmngt($int,
  bool, V_OBF__bbcc, b_bool))) & infix_eqeq($int, dom($int,
  bool, V_OBF__nncc), V_OBF__bbcc)) & (V_OBF__ddbb = 2))
  & (V_OBF__eebb = V_OBF__hhbb)) & (V_OBF__vv = V_OBF__ssbb))
  & (V_OBF__yybb = false)))).

tff(f15, type, f15: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f15_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f15(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__tt,
  V_OBF__jjcc)) & mem(set(tuple2($int, $int)), V_OBF__ggcc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__cccc)))
  & infix_eqeq($int, dom($int, $int, V_OBF__ggcc), V_OBF__bbcc))
  & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f16, type, f16: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f16_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f16(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> mem(set(tuple2($int, $int)), V_OBF__iicc,
  relation($int, $int, V_OBF__bbcc,
  union($int, union($int, singleton($int, V_OBF__ggbb),
  singleton($int, V_OBF__hhbb)), singleton($int, V_OBF__ffbb)))))).

tff(f17, type, f17: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f17_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f17(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__tt,
  V_OBF__hhcc)) & mem(set(tuple2($int, $int)), V_OBF__ggcc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__cccc)))
  & infix_eqeq($int, dom($int, $int, V_OBF__ggcc), V_OBF__bbcc))
  & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f18, type, f18: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f18_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f18(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__tt,
  V_OBF__ffcc)) & mem(set(tuple2($int, $int)), V_OBF__ggcc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__cccc)))
  & infix_eqeq($int, dom($int, $int, V_OBF__ggcc), V_OBF__bbcc))
  & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f19, type, f19: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f19_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f19(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__tt,
  V_OBF__eecc)) & mem(set(tuple2($int, $int)), V_OBF__aacc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__cccc)))
  & infix_eqeq($int, dom($int, $int, V_OBF__aacc), V_OBF__bbcc))
  & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f20, type, f20: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f20_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f20(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__tt,
  V_OBF__ddcc)) & mem(set(tuple2($int, $int)), V_OBF__aacc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__cccc)))
  & infix_eqeq($int, dom($int, $int, V_OBF__aacc), V_OBF__bbcc))
  & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f21, type, f21: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f21_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f21(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__tt,
  V_OBF__zzbb)) & mem(set(tuple2($int, $int)), V_OBF__aacc,
  infix_plmngt($int, $int, V_OBF__bbcc, V_OBF__cccc)))
  & infix_eqeq($int, dom($int, $int, V_OBF__aacc), V_OBF__bbcc))
  & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f22, type, f22: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f22_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f22(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem(set($int), V_OBF__vvbb,
  power($int, V_OBF__bbbb))) & mem(set($int), V_OBF__wwbb,
  power($int, V_OBF__bbbb))) & (V_OBF__ddbb = 2))
  & (V_OBF__eebb = V_OBF__hhbb)) & (V_OBF__tt = V_OBF__xxbb))
  & (V_OBF__vv = V_OBF__ssbb)) & (V_OBF__yybb = false)))).

tff(f23, type, f23: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f23_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f23(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((($true & mem($int, V_OBF__vv,
  V_OBF__ttbb)) & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__tt = V_OBF__oobb)) & (V_OBF__kkbb = V_OBF__llbb)))).

tff(f24, type, f24: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f24_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f24(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> mem($int, V_OBF__tt,
  union($int, singleton($int, V_OBF__oobb), singleton($int, V_OBF__ppbb))))).

tff(f25, type, f25: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f25_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f25(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb)
  <=> mem(set(enum_OBF__ii), diff(enum_OBF__ii, V_OBF__uubb,
  union(enum_OBF__ii, union(enum_OBF__ii, union(enum_OBF__ii, union(enum_OBF__ii, union(enum_OBF__ii, union(enum_OBF__ii, union(enum_OBF__ii, singleton(enum_OBF__ii, e_OBF__qq),
  singleton(enum_OBF__ii, e_OBF__pp)), singleton(enum_OBF__ii, e_OBF__oo)),
  singleton(enum_OBF__ii, e_OBF__nn)), singleton(enum_OBF__ii, e_OBF__mm)),
  singleton(enum_OBF__ii, e_OBF__ll)), singleton(enum_OBF__ii, e_OBF__kk)),
  singleton(enum_OBF__ii, e_OBF__jj))), power(enum_OBF__ii, V_OBF__uubb)))).

tff(f26, type, f26: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f26_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f26(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((($true & mem($int, V_OBF__vv,
  V_OBF__ttbb)) & (V_OBF__ddbb = 2)) & (V_OBF__eebb = V_OBF__hhbb))
  & (V_OBF__tt = V_OBF__ppbb)) & (V_OBF__kkbb = V_OBF__llbb)))).

tff(f27, type, f27: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f27_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f27(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb)
  <=> mem(set(enum_OBF__ii), diff(enum_OBF__ii, V_OBF__uubb,
  union(enum_OBF__ii, singleton(enum_OBF__ii, e_OBF__ss),
  singleton(enum_OBF__ii, e_OBF__rr))), power(enum_OBF__ii, V_OBF__uubb)))).

tff(f28, type, f28: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f28_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f28(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> (((((((((($true & mem($int, V_OBF__eebb,
  union($int, singleton($int, V_OBF__ggbb), singleton($int, V_OBF__hhbb))))
  & mem($int, V_OBF__tt, union($int, union($int, V_OBF__mmbb, V_OBF__nnbb),
  union($int, union($int, union($int, singleton($int, V_OBF__oobb),
  singleton($int, V_OBF__ppbb)), singleton($int, V_OBF__qqbb)),
  singleton($int, V_OBF__rrbb))))) & (mem($int, V_OBF__tt, V_OBF__mmbb) => ~
  (V_OBF__vv = V_OBF__ssbb))) & (mem($int, V_OBF__tt, V_OBF__nnbb) => ~
  mem($int, V_OBF__vv, V_OBF__ttbb))) & ((mem($int, V_OBF__tt,
  union($int, singleton($int, V_OBF__oobb), singleton($int, V_OBF__ppbb)))
  & mem($int, V_OBF__vv, V_OBF__ttbb)) => ((V_OBF__eebb = V_OBF__hhbb) & ~
  (V_OBF__kkbb = V_OBF__llbb)))) & ((V_OBF__tt = V_OBF__qqbb)
  => (V_OBF__eebb = V_OBF__hhbb))) & ((V_OBF__tt = V_OBF__rrbb) => ~
  (V_OBF__vv = V_OBF__ssbb))) & (V_OBF__ddbb = 2)) & mem($int, V_OBF__tt,
  union($int, singleton($int, V_OBF__oobb), singleton($int, V_OBF__ppbb))))
  & mem($int, V_OBF__vv, V_OBF__ttbb)))).

tff(f30, type, f30: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f30_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f30(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ~ (V_OBF__kkbb = V_OBF__llbb))).

tff(f33, type, f33: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f33_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f33(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ((((((($true & mem($int, V_OBF__eebb,
  union($int, union($int, singleton($int, V_OBF__ggbb),
  singleton($int, V_OBF__hhbb)), singleton($int, V_OBF__ffbb))))
  & mem($int, V_OBF__tt, V_OBF__uu)) & (((V_OBF__eebb = V_OBF__ggbb)
  & mem($int, V_OBF__tt, V_OBF__iibb)) => ~ (V_OBF__xx = 1)))
  & (V_OBF__ddbb = 2)) & infix_eqeq($int, V_OBF__jjbb, empty($int)))
  & mem($int, V_OBF__tt, V_OBF__iibb)) & (V_OBF__eebb = V_OBF__ggbb)))).

tff(f34, type, f34: (set(tuple2($int, $int)) * set($int) * enum_OBF__aa *
  set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set($int) * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * $int *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set($int) * $int * set(tuple2($int, $int)) * bool *
  set(tuple2($int, $int)) * $int * set(enum_OBF__ii) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set($int) * set(tuple2($int, bool)) *
  $int * set(tuple2($int, $int)) * bool *
  set(tuple2(tuple2($int, $int), $int)) * set($int) * $int * set($int) *
  $int * set(tuple2($int, $int)) * set(tuple2($int, bool)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, bool)) * $int * set(tuple2($int, $int)) * set($int) *
  $int * set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set($int) * set($int) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, bool)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * bool * set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(enum_OBF__ii) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) * $int *
  set($int) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set($int) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) *
  set(tuple2($int, $int)) * set($int) * set($int) * set(tuple2($int, $int)) *
  set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int) > $o).

tff(f34_def, axiom, ![V_OBF__zzff:set(tuple2($int, $int)), V_OBF__zzee:
  set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int), V_OBF__zzbb:
  set($int), V_OBF__zz:set($int), V_OBF__yyff:set(tuple2($int, $int)),
  V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:$int, V_OBF__yycc:
  set($int), V_OBF__yybb:bool, V_OBF__yy:set($int), V_OBF__xxff:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:set(tuple2($int, $int)),
  V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:set($int), V_OBF__xxbb:
  $int, V_OBF__xx:$int, V_OBF__wwff:set(tuple2($int, $int)), V_OBF__wwee:
  set($int), V_OBF__wwdd:$int, V_OBF__wwcc:set(tuple2($int, $int)),
  V_OBF__wwbb:set($int), V_OBF__ww:set($int), V_OBF__vvff:set($int),
  V_OBF__vvee:set($int), V_OBF__vvdd:set(tuple2($int, $int)), V_OBF__vvcc:
  set($int), V_OBF__vvbb:set($int), V_OBF__vv:$int, V_OBF__uuff:
  set(tuple2($int, $int)), V_OBF__uuee:bool, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:set(enum_OBF__ii),
  V_OBF__uu:set($int), V_OBF__ttff:set(tuple2($int, $int)), V_OBF__ttee:
  set(tuple2($int, $int)), V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set($int), V_OBF__tt:$int,
  V_OBF__ssff:set(tuple2($int, $int)), V_OBF__ssee:set(tuple2($int, $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:set(tuple2($int, $int)), V_OBF__ssbb:$int,
  V_OBF__rrff:set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int,
  V_OBF__rrcc:set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: (f34(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) <=> ~ (V_OBF__xx = 1))).

tff(oBF__gggg_1, conjecture, ![V_OBF__zzff:set(tuple2($int, $int)),
  V_OBF__zzee:set($int), V_OBF__zzdd:enum_OBF__aa, V_OBF__zzcc:set($int),
  V_OBF__zzbb:set($int), V_OBF__zz:set($int), V_OBF__yyff:
  set(tuple2($int, $int)), V_OBF__yyee:set(tuple2($int, $int)), V_OBF__yydd:
  $int, V_OBF__yycc:set($int), V_OBF__yybb:bool, V_OBF__yy:set($int),
  V_OBF__xxff:set(tuple2(tuple2($int, $int), $int)), V_OBF__xxee:
  set(tuple2($int, $int)), V_OBF__xxdd:set(tuple2($int, $int)), V_OBF__xxcc:
  set($int), V_OBF__xxbb:$int, V_OBF__xx:$int, V_OBF__wwff:
  set(tuple2($int, $int)), V_OBF__wwee:set($int), V_OBF__wwdd:$int,
  V_OBF__wwcc:set(tuple2($int, $int)), V_OBF__wwbb:set($int), V_OBF__ww:
  set($int), V_OBF__vvff:set($int), V_OBF__vvee:set($int), V_OBF__vvdd:
  set(tuple2($int, $int)), V_OBF__vvcc:set($int), V_OBF__vvbb:set($int),
  V_OBF__vv:$int, V_OBF__uuff:set(tuple2($int, $int)), V_OBF__uuee:bool,
  V_OBF__uudd:set(tuple2($int, $int)), V_OBF__uucc:$int, V_OBF__uubb:
  set(enum_OBF__ii), V_OBF__uu:set($int), V_OBF__ttff:
  set(tuple2($int, $int)), V_OBF__ttee:set(tuple2($int, $int)), V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set($int), V_OBF__tt:$int, V_OBF__ssff:set(tuple2($int, $int)),
  V_OBF__ssee:set(tuple2($int, $int)), V_OBF__ssdd:$int, V_OBF__sscc:
  set(tuple2($int, $int)), V_OBF__ssbb:$int, V_OBF__rrff:
  set(tuple2($int, $int)), V_OBF__rree:$int, V_OBF__rrdd:$int, V_OBF__rrcc:
  set(tuple2($int, $int)), V_OBF__rrbb:$int, V_OBF__qqff:
  set(tuple2($int, $int)), V_OBF__qqee:$int, V_OBF__qqdd:
  set(tuple2($int, $int)), V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:
  $int, V_OBF__ppff:set(tuple2($int, $int)), V_OBF__ppee:$int, V_OBF__ppdd:
  set($int), V_OBF__ppcc:set(tuple2($int, bool)), V_OBF__ppbb:$int,
  V_OBF__ooff:set(tuple2($int, $int)), V_OBF__ooee:bool, V_OBF__oodd:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc:set($int), V_OBF__oobb:
  $int, V_OBF__nnff:set($int), V_OBF__nnee:$int, V_OBF__nndd:
  set(tuple2($int, $int)), V_OBF__nncc:set(tuple2($int, bool)), V_OBF__nnbb:
  set($int), V_OBF__mmff:set(tuple2($int, $int)), V_OBF__mmee:$int,
  V_OBF__mmdd:set(tuple2($int, $int)), V_OBF__mmcc:set(tuple2($int, $int)),
  V_OBF__mmbb:set($int), V_OBF__llff:set(tuple2($int, $int)), V_OBF__llee:
  $int, V_OBF__lldd:set(tuple2($int, $int)), V_OBF__llcc:
  set(tuple2($int, $int)), V_OBF__llbb:$int, V_OBF__kkff:
  set(tuple2($int, bool)), V_OBF__kkee:$int, V_OBF__kkdd:
  set(tuple2($int, $int)), V_OBF__kkcc:set($int), V_OBF__kkbb:$int,
  V_OBF__jjff:set(tuple2($int, $int)), V_OBF__jjee:$int, V_OBF__jjdd:
  set(tuple2($int, $int)), V_OBF__jjcc:set($int), V_OBF__jjbb:set($int),
  V_OBF__iiff:set(tuple2($int, $int)), V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set(tuple2($int, $int)), V_OBF__iibb:
  set($int), V_OBF__hhff:set(tuple2($int, bool)), V_OBF__hhee:
  set(tuple2($int, $int)), V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:
  set($int), V_OBF__hhbb:$int, V_OBF__ggff:set(tuple2($int, $int)),
  V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:set(tuple2($int, $int)),
  V_OBF__ggcc:set(tuple2($int, $int)), V_OBF__ggbb:$int, V_OBF__ffgg:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ffff:
  set(tuple2($int, $int)), V_OBF__ffee:bool, V_OBF__ffdd:set($int),
  V_OBF__ffcc:set($int), V_OBF__ffbb:$int, V_OBF__eegg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__eeff:
  set(enum_OBF__ii), V_OBF__eeee:$int, V_OBF__eedd:set($int), V_OBF__eecc:
  set($int), V_OBF__eebb:$int, V_OBF__ddgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ddff:set($int),
  V_OBF__ddee:$int, V_OBF__dddd:set($int), V_OBF__ddcc:set($int),
  V_OBF__ddbb:$int, V_OBF__ccgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ccff:set($int),
  V_OBF__ccee:$int, V_OBF__ccdd:set($int), V_OBF__cccc:set($int),
  V_OBF__ccbb:$int, V_OBF__bbgg:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__bbff:set($int),
  V_OBF__bbee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__bbdd:set(tuple2($int, $int)), V_OBF__bbcc:set($int), V_OBF__bbbb:
  set($int), V_OBF__aagg:set(tuple2($int, $int)), V_OBF__aaff:set($int),
  V_OBF__aaee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd:
  set(tuple2($int, $int)), V_OBF__aacc:set(tuple2($int, $int)), V_OBF__aabb:
  $int]: ((f1(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc,
  V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc,
  V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc,
  V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc,
  V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff,
  V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg,
  V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) & (f2(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd,
  V_OBF__yycc, V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd,
  V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd,
  V_OBF__vvcc, V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd,
  V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd,
  V_OBF__sscc, V_OBF__ssbb, V_OBF__rrff, V_OBF__rree, V_OBF__rrdd,
  V_OBF__rrcc, V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd,
  V_OBF__qqcc, V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee, V_OBF__oodd,
  V_OBF__oocc, V_OBF__oobb, V_OBF__nnff, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd,
  V_OBF__mmcc, V_OBF__mmbb, V_OBF__llff, V_OBF__llee, V_OBF__lldd,
  V_OBF__llcc, V_OBF__llbb, V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd,
  V_OBF__kkcc, V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee, V_OBF__iidd,
  V_OBF__iicc, V_OBF__iibb, V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd,
  V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee,
  V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg,
  V_OBF__ddff, V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__ccgg, V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc,
  V_OBF__ccbb, V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd,
  V_OBF__bbcc, V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff, V_OBF__aaee,
  V_OBF__aadd, V_OBF__aacc, V_OBF__aabb) & (f3(V_OBF__zzff, V_OBF__zzee,
  V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yyff, V_OBF__yyee,
  V_OBF__yydd, V_OBF__yycc, V_OBF__yybb, V_OBF__yy, V_OBF__xxff, V_OBF__xxee,
  V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwff, V_OBF__wwee,
  V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvff, V_OBF__vvee,
  V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb, V_OBF__vv, V_OBF__uuff, V_OBF__uuee,
  V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttff, V_OBF__ttee,
  V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssff, V_OBF__ssee,
  V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb, V_OBF__rrff, V_OBF__rree,
  V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb, V_OBF__qqff, V_OBF__qqee,
  V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__ppff, V_OBF__ppee,
  V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__ooff, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__nnff, V_OBF__nnee,
  V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb, V_OBF__mmff, V_OBF__mmee,
  V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb, V_OBF__llff, V_OBF__llee,
  V_OBF__lldd, V_OBF__llcc, V_OBF__llbb, V_OBF__kkff, V_OBF__kkee,
  V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__jjff, V_OBF__jjee,
  V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__iiff, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__hhff, V_OBF__hhee,
  V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggff, V_OBF__ggee,
  V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffgg, V_OBF__ffff,
  V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb, V_OBF__eegg,
  V_OBF__eeff, V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb,
  V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc,
  V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg, V_OBF__bbff, V_OBF__bbee,
  V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aagg, V_OBF__aaff,
  V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb) & ($true & $true))))
  => (f5(V_OBF__zzff, V_OBF__zzee, V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yyff, V_OBF__yyee, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxff, V_OBF__xxee, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwff, V_OBF__wwee, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvff, V_OBF__vvee, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uuff, V_OBF__uuee, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttff, V_OBF__ttee, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssff, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__rrff, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__qqff, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb,
  V_OBF__ppff, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__ooff, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb,
  V_OBF__nnff, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__mmff, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__llff, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__kkff, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb,
  V_OBF__jjff, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__iiff, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb,
  V_OBF__hhff, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggff, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffgg, V_OBF__ffff, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eegg, V_OBF__eeff, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddgg, V_OBF__ddff, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccgg, V_OBF__ccff,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbgg,
  V_OBF__bbff, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aagg, V_OBF__aaff, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc,
  V_OBF__aabb) & $true))).
