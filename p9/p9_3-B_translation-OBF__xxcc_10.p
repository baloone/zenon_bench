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

tff(f1, type, f1: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f1_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f1(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb)
  <=> (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem($int, V_OBF__qq, integer))
  & infix_eqeq(tuple2($int, $int), V_OBF__eecc, times($int, $int, V_OBF__tt,
  V_OBF__ss))) & infix_eqeq(tuple2($int, $int), V_OBF__ddcc, times($int,
  $int, V_OBF__tt, V_OBF__ss))) & $lesseq(1,V_OBF__qq)) & $true)
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjcc,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkcc,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llcc,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mmcc,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mmbb,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__jjcc,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 0),
  union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__bb),
  singleton(enum_OBF__aa, e_OBF__ff)), singleton(enum_OBF__aa, e_OBF__gg)),
  singleton(enum_OBF__aa, e_OBF__ee)), singleton(enum_OBF__aa, e_OBF__cc))),
  singleton($int, 0))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__kkcc,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 0),
  union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__hh),
  singleton(enum_OBF__aa, e_OBF__dd))), singleton($int, 1))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__llcc,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 1), singleton(enum_OBF__aa, e_OBF__cc)),
  singleton($int, 0))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__mmcc,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 1),
  union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__bb),
  singleton(enum_OBF__aa, e_OBF__ff)), singleton(enum_OBF__aa, e_OBF__gg)),
  singleton(enum_OBF__aa, e_OBF__ee)), singleton(enum_OBF__aa, e_OBF__hh)),
  singleton(enum_OBF__aa, e_OBF__dd))), singleton($int, 1))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__mmbb,
  union(tuple2(tuple2($int, enum_OBF__aa), $int), union(tuple2(tuple2($int,
                                                               enum_OBF__aa),
                                                        $int), union(
  tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__jjcc, V_OBF__kkcc),
  V_OBF__llcc), V_OBF__mmcc))) & $true) & $true)
  & mem(set(tuple2($int, $int)), V_OBF__nncc,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__oocc,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__tt, V_OBF__ss), V_OBF__nnbb))))
  & mem(set(tuple2($int, $int)), V_OBF__ppcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & mem(set(tuple2($int, $int)), V_OBF__eecc,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & mem(set(tuple2($int, $int)), V_OBF__ddcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__qqcc,
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
  $int, times(tuple2($int, $int), $int, V_OBF__nncc, V_OBF__nnbb),
  singleton($int, V_OBF__jjbb)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__oocc, singleton($int, V_OBF__hhbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__ppcc, V_OBF__nnbb), singleton($int, V_OBF__ccbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__eecc, V_OBF__nnbb), singleton($int, V_OBF__xx))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__ddcc, V_OBF__nnbb), singleton($int, V_OBF__oo))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__tt, V_OBF__ss), V_OBF__nnbb),
  singleton($int, V_OBF__iibb)))))
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqcc,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__tt,
  V_OBF__ss), V_OBF__nnbb), V_OBF__ppbb)))) & mem($int, V_OBF__jjbb,
  V_OBF__ppbb)) & mem($int, V_OBF__hhbb, V_OBF__ppbb))
  & mem($int, V_OBF__ccbb, V_OBF__ppbb)) & mem($int, V_OBF__xx, V_OBF__ppbb))
  & mem($int, V_OBF__oo, V_OBF__ppbb)) & mem($int, V_OBF__iibb, V_OBF__ppbb))
  & ~ (V_OBF__jjbb = V_OBF__hhbb)) & ~ (V_OBF__jjbb = V_OBF__ccbb)) & ~
  (V_OBF__jjbb = V_OBF__xx)) & ~ (V_OBF__jjbb = V_OBF__oo)) & ~
  (V_OBF__jjbb = V_OBF__iibb)) & ~ (V_OBF__hhbb = V_OBF__jjbb)) & ~
  (V_OBF__hhbb = V_OBF__ccbb)) & ~ (V_OBF__hhbb = V_OBF__xx)) & ~
  (V_OBF__hhbb = V_OBF__oo)) & ~ (V_OBF__hhbb = V_OBF__iibb)) & ~
  (V_OBF__ccbb = V_OBF__jjbb)) & ~ (V_OBF__ccbb = V_OBF__hhbb)) & ~
  (V_OBF__ccbb = V_OBF__xx)) & ~ (V_OBF__ccbb = V_OBF__oo)) & ~
  (V_OBF__ccbb = V_OBF__iibb)) & ~ (V_OBF__xx = V_OBF__jjbb)) & ~
  (V_OBF__xx = V_OBF__hhbb)) & ~ (V_OBF__xx = V_OBF__ccbb)) & ~
  (V_OBF__xx = V_OBF__oo)) & ~ (V_OBF__xx = V_OBF__iibb)) & ~
  (V_OBF__oo = V_OBF__jjbb)) & ~ (V_OBF__oo = V_OBF__hhbb)) & ~
  (V_OBF__oo = V_OBF__ccbb)) & ~ (V_OBF__oo = V_OBF__xx)) & ~
  (V_OBF__oo = V_OBF__iibb)) & ~ (V_OBF__iibb = V_OBF__jjbb)) & ~
  (V_OBF__iibb = V_OBF__hhbb)) & ~ (V_OBF__iibb = V_OBF__ccbb)) & ~
  (V_OBF__iibb = V_OBF__xx)) & ~ (V_OBF__iibb = V_OBF__oo))
  & mem(set($int), V_OBF__tt, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__tt, empty($int))) & mem(set($int), V_OBF__ss,
  finite_subsets($int, integer))) & ~ infix_eqeq($int, V_OBF__ss,
  empty($int))) & mem(set($int), V_OBF__nnbb, finite_subsets($int, integer)))
  & ~ infix_eqeq($int, V_OBF__nnbb, empty($int)))
  & mem(set($int), V_OBF__ppbb, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__ppbb, empty($int))))).

tff(f2, type, f2: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f2_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f2(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((((((((($true & mem($int, V_OBF__ffcc, V_OBF__tt))
  & mem($int, V_OBF__eebb, V_OBF__ss)) & mem($int, V_OBF__ggcc, V_OBF__nnbb))
  & mem($int, V_OBF__hhcc, V_OBF__ppbb)) & mem($int, V_OBF__iicc, V_OBF__ss))
  & mem(set(tuple2($int, $int)), V_OBF__cccc, infix_plmngt($int, $int, mk(1,
  V_OBF__qq), V_OBF__ss))) & infix_eqeq($int, dom($int, $int, V_OBF__cccc),
  mk(1, V_OBF__qq))) & mem(set(tuple2($int, $int)), V_OBF__bbcc,
  infix_plmngt($int, $int, mk(1, V_OBF__qq), V_OBF__ss)))
  & infix_eqeq($int, dom($int, $int, V_OBF__bbcc), mk(1, V_OBF__qq))))).

tff(f3, type, f3: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f3_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f3(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ($true & $true))).

tff(f4, type, f4: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f4_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f4(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq(tuple2($int, $int), dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__qq, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, 0, 1)))), V_OBF__eecc))).

tff(f5, type, f5: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f5_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f5(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ($true & $true))).

tff(f6, type, f6: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f6_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f6(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq(tuple2($int, $int), dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss),
  singleton(tuple2($int, $int), tuple21($int, $int, 0, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, 0, 1)))), V_OBF__ddcc))).

tff(f8, type, f8: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f8_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f8(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), V_OBF__cccc, relation($int,
  $int, integer, V_OBF__ss)))).

tff(f10, type, f10: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f10_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f10(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), V_OBF__bbcc, relation($int,
  $int, integer, V_OBF__ss)))).

tff(f12, type, f12: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f12_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f12(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, 0, mk(0, V_OBF__qq)))).

tff(f13, type, f13: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f13_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f13(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((((((((((((((((((((((((((((((((((((((((((($true
  & mem($int, V_OBF__kkbb, integer)) & $true) & mem($int, V_OBF__pp,
  integer)) & mem(tuple2(tuple2($int, enum_OBF__aa), $int), tuple21($int,
  tuple2($int, enum_OBF__aa), tuple21(enum_OBF__aa, $int, V_OBF__kkbb,
  V_OBF__llbb), V_OBF__pp), V_OBF__mmbb))
  & mem(set(tuple2($int, $int)), V_OBF__zz,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__ggbb,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__tt, V_OBF__ss), V_OBF__nnbb))))
  & mem(set(tuple2($int, $int)), V_OBF__yy,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & mem(set(tuple2($int, $int)), V_OBF__ww,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & mem(set(tuple2($int, $int)), V_OBF__kk,
  power(tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__oobb,
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
  $int, times(tuple2($int, $int), $int, V_OBF__zz, V_OBF__nnbb),
  singleton($int, V_OBF__jjbb)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__ggbb, singleton($int, V_OBF__hhbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__yy, V_OBF__nnbb), singleton($int, V_OBF__ccbb))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__ww, V_OBF__nnbb), singleton($int, V_OBF__xx))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__kk, V_OBF__nnbb), singleton($int, V_OBF__oo))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__tt, V_OBF__ss), V_OBF__nnbb),
  singleton($int, V_OBF__iibb))))) & mem($int, V_OBF__mm, integer))
  & mem($int, V_OBF__ii, V_OBF__tt)) & mem($int, V_OBF__jj, V_OBF__ss))
  & mem($int, V_OBF__ffbb, V_OBF__nnbb)) & mem($int, V_OBF__nn, V_OBF__ppbb))
  & $true)
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oobb,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__tt,
  V_OBF__ss), V_OBF__nnbb), V_OBF__ppbb)))) & $true)
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mmbb,
  infix_plmngt(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, union($int, singleton($int, 0), singleton($int, 1)),
  set_enum_OBF__aa), union($int, singleton($int, 0), singleton($int, 1)))))
  & infix_eqeq(tuple2($int, enum_OBF__aa), dom(tuple2($int, enum_OBF__aa),
  $int, V_OBF__mmbb), times($int,
  enum_OBF__aa, union($int, singleton($int, 0), singleton($int, 1)),
  set_enum_OBF__aa))) & mem($int, V_OBF__pp, union($int, singleton($int, 0),
  singleton($int, 1)))) & $true) & mem($int, V_OBF__aabb, V_OBF__ss))
  & mem($int, V_OBF__ll, integer)) & mem(set(tuple2($int, $int)), V_OBF__uu,
  relation($int, $int, integer, V_OBF__ss)))
  & mem(set(tuple2($int, $int)), V_OBF__rr, relation($int, $int, integer,
  V_OBF__ss))) & infix_eqeq(tuple2($int, $int), V_OBF__ww,
  dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__qq, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__ll,
  V_OBF__pp)))))) & infix_eqeq(tuple2($int, $int), V_OBF__kk,
  dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss),
  singleton(tuple2($int, $int), tuple21($int, $int, 0, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__ll,
  V_OBF__pp)))))) & mem($int, V_OBF__ll, mk(0, V_OBF__qq)))
  & mem(set(tuple2($int, $int)), V_OBF__uu, infix_plmngt($int, $int, mk(1,
  V_OBF__qq), V_OBF__ss))) & infix_eqeq($int, dom($int, $int, V_OBF__uu),
  mk(1, V_OBF__qq))) & mem(set(tuple2($int, $int)), V_OBF__rr,
  infix_plmngt($int, $int, mk(1, V_OBF__qq), V_OBF__ss)))
  & infix_eqeq($int, dom($int, $int, V_OBF__rr), mk(1, V_OBF__qq)))
  & (V_OBF__rrbb = V_OBF__mm)) & (V_OBF__ssbb = V_OBF__ii))
  & (V_OBF__ttbb = V_OBF__jj)) & (V_OBF__uubb = V_OBF__ffbb))
  & (V_OBF__vvbb = V_OBF__nn)) & (V_OBF__wwbb = V_OBF__qqbb))
  & infix_eqeq(tuple2($int, $int), V_OBF__xxbb, V_OBF__zz))
  & infix_eqeq(tuple2(tuple2($int, $int), $int), V_OBF__yybb, V_OBF__ggbb))
  & infix_eqeq(tuple2($int, $int), V_OBF__zzbb, V_OBF__yy))
  & (V_OBF__aacc = V_OBF__pp)))).

tff(f14, type, f14: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f14_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f14(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ($true & $true))).

tff(f15, type, f15: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f15_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f15(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ($true & $true))).

tff(f19, type, f19: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f19_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f19(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((($true & ~ mem(tuple2($int, $int), tuple21($int,
  $int, V_OBF__ii, V_OBF__jj), V_OBF__zz)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__jjbb)))).

tff(f21, type, f21: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f21_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f21(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ~ (V_OBF__nn = V_OBF__iibb))).

tff(f22, type, f22: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f22_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f22(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((($true & ~
  mem(tuple2(tuple2($int, $int), $int), tuple21($int,
  tuple2($int, $int), tuple21($int, $int, V_OBF__ii, V_OBF__jj),
  V_OBF__ffbb), V_OBF__ggbb)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__hhbb)))).

tff(f23, type, f23: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f23_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f23(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> (((((($true & mem(tuple2($int, $int), tuple21($int,
  $int, V_OBF__ii, V_OBF__jj), V_OBF__yy))
  & mem(tuple2($int, $int), tuple21($int, $int, V_OBF__eebb, V_OBF__ddbb),
  infix_lspl($int, $int, times($int, $int, V_OBF__ss,
  singleton($int, V_OBF__jj)), singleton(tuple2($int, $int), tuple21($int,
  $int, V_OBF__jj, V_OBF__aabb)))))
  & mem(set(tuple2($int, $int)), V_OBF__bbbb, relation($int, $int, V_OBF__tt,
  V_OBF__ss))) & mem(set(tuple2($int, $int)), V_OBF__vv, relation($int,
  $int, V_OBF__tt, V_OBF__ss))) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__ccbb)))).

tff(f25, type, f25: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f25_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f25(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__tt, V_OBF__ss),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__qq, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__ll, 0)))),
  relation($int, $int, V_OBF__tt, V_OBF__ss)))).

tff(f29, type, f29: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f29_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f29(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((($true & ~ mem(tuple2($int, $int), tuple21($int,
  $int, V_OBF__ii, V_OBF__jj), V_OBF__yy)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__ccbb)))).

tff(f30, type, f30: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f30_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f30(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> (((((($true & $lesseq($sum(V_OBF__ll,1),V_OBF__qq))
  & mem(set(tuple2($int, $int)), V_OBF__bbbb, relation($int, $int, V_OBF__tt,
  V_OBF__ss))) & mem(set(tuple2($int, $int)), V_OBF__vv, relation($int,
  $int, V_OBF__tt, V_OBF__ss))) & (V_OBF__mm = 2)) & (V_OBF__nn = V_OBF__xx))
  & (V_OBF__pp = 0)))).

tff(f31, type, f31: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f31_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f31(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(tuple2($int, $int), tuple21($int, $int, V_OBF__ii,
  V_OBF__jj), V_OBF__ww))).

tff(f35, type, f35: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f35_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f35(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, $sum(V_OBF__ll,1), integer))).

tff(f36, type, f36: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f36_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f36(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), infix_lspl($int,
  $int, V_OBF__uu, singleton(tuple2($int, $int), tuple21($int,
  $int, $sum(V_OBF__ll,1), V_OBF__jj))), relation($int, $int, integer,
  V_OBF__ss)))).

tff(f37, type, f37: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f37_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f37(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), infix_lspl($int,
  $int, V_OBF__rr, singleton(tuple2($int, $int), tuple21($int,
  $int, $sum(V_OBF__ll,1), V_OBF__aabb))), relation($int, $int, integer,
  V_OBF__ss)))).

tff(f38, type, f38: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f38_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f38(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, $sum(V_OBF__ll,1), mk(0, V_OBF__qq)))).

tff(f40, type, f40: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f40_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f40(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), infix_lspl($int,
  $int, V_OBF__uu, singleton(tuple2($int, $int), tuple21($int,
  $int, $sum(V_OBF__ll,1), V_OBF__jj))), infix_plmngt($int, $int, mk(1,
  V_OBF__qq), V_OBF__ss)))).

tff(f41, type, f41: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f41_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f41(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq($int, dom($int, $int, infix_lspl($int,
  $int, V_OBF__uu, singleton(tuple2($int, $int), tuple21($int,
  $int, $sum(V_OBF__ll,1), V_OBF__jj)))), mk(1, V_OBF__qq)))).

tff(f43, type, f43: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f43_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f43(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(set(tuple2($int, $int)), infix_lspl($int,
  $int, V_OBF__rr, singleton(tuple2($int, $int), tuple21($int,
  $int, $sum(V_OBF__ll,1), V_OBF__aabb))), infix_plmngt($int, $int, mk(1,
  V_OBF__qq), V_OBF__ss)))).

tff(f44, type, f44: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f44_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f44(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> infix_eqeq($int, dom($int, $int, infix_lspl($int,
  $int, V_OBF__rr, singleton(tuple2($int, $int), tuple21($int,
  $int, $sum(V_OBF__ll,1), V_OBF__aabb)))), mk(1, V_OBF__qq)))).

tff(f45, type, f45: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f45_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f45(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((($true & (V_OBF__pp = 1)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__xx)))).

tff(f50, type, f50: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f50_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f50(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> (((($true & (V_OBF__ll = V_OBF__qq)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__xx)) & (V_OBF__pp = 0)))).

tff(f51, type, f51: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f51_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f51(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ~ mem(tuple2($int, $int), tuple21($int, $int, V_OBF__ii,
  V_OBF__jj), V_OBF__ww))).

tff(f52, type, f52: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f52_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f52(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((((($true & $lesseq(1,V_OBF__ll))
  & mem(set(tuple2($int, $int)), V_OBF__vv, relation($int, $int, V_OBF__tt,
  V_OBF__ss))) & (V_OBF__mm = 2)) & (V_OBF__nn = V_OBF__oo))
  & (V_OBF__pp = 0)))).

tff(f53, type, f53: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f53_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f53(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem(tuple2($int, $int), tuple21($int, $int, V_OBF__ii,
  V_OBF__jj), V_OBF__kk))).

tff(f54, type, f54: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f54_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f54(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, apply($int, $int, V_OBF__uu, V_OBF__ll),
  V_OBF__ss))).

tff(f57, type, f57: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f57_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f57(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, apply($int, $int, V_OBF__rr, V_OBF__ll),
  V_OBF__ss))).

tff(f58, type, f58: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f58_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f58(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, $difference(V_OBF__ll,1), integer))).

tff(f59, type, f59: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f59_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f59(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> mem($int, $difference(V_OBF__ll,1), mk(0, V_OBF__qq)))).

tff(f60, type, f60: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f60_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f60(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ((($true & (V_OBF__pp = 1)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__oo)))).

tff(f61, type, f61: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f61_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f61(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> (((($true & (0 = V_OBF__ll)) & (V_OBF__mm = 2))
  & (V_OBF__nn = V_OBF__oo)) & (V_OBF__pp = 0)))).

tff(f62, type, f62: (set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * bool * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set($int) * $int * set($int) * $int * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, $int), $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * enum_OBF__aa * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * $int * $int * $int * $int * $int * $int *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * $int) > $o).

tff(f62_def, axiom, ![V_OBF__zzbb:set(tuple2($int, $int)), V_OBF__zz:
  set(tuple2($int, $int)), V_OBF__yybb:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__yy:set(tuple2($int, $int)), V_OBF__xxbb:set(tuple2($int, $int)),
  V_OBF__xx:$int, V_OBF__wwbb:bool, V_OBF__ww:set(tuple2($int, $int)),
  V_OBF__vvbb:$int, V_OBF__vv:set(tuple2($int, $int)), V_OBF__uubb:$int,
  V_OBF__uu:set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: (f62(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) <=> ~ mem(tuple2($int, $int), tuple21($int, $int, V_OBF__ii,
  V_OBF__jj), V_OBF__kk))).

tff(oBF__xxcc_10, conjecture, ![V_OBF__zzbb:set(tuple2($int, $int)),
  V_OBF__zz:set(tuple2($int, $int)), V_OBF__yybb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__yy:set(tuple2($int, $int)),
  V_OBF__xxbb:set(tuple2($int, $int)), V_OBF__xx:$int, V_OBF__wwbb:bool,
  V_OBF__ww:set(tuple2($int, $int)), V_OBF__vvbb:$int, V_OBF__vv:
  set(tuple2($int, $int)), V_OBF__uubb:$int, V_OBF__uu:
  set(tuple2($int, $int)), V_OBF__ttbb:$int, V_OBF__tt:set($int),
  V_OBF__ssbb:$int, V_OBF__ss:set($int), V_OBF__rrbb:$int, V_OBF__rr:
  set(tuple2($int, $int)), V_OBF__qqcc:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__qqbb:bool,
  V_OBF__qq:$int, V_OBF__ppcc:set(tuple2($int, $int)), V_OBF__ppbb:set($int),
  V_OBF__pp:$int, V_OBF__oocc:set(tuple2(tuple2($int, $int), $int)),
  V_OBF__oobb:set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__oo:
  $int, V_OBF__nncc:set(tuple2($int, $int)), V_OBF__nnbb:set($int),
  V_OBF__nn:$int, V_OBF__mmcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__mmbb:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__mm:$int,
  V_OBF__llcc:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__llbb:
  enum_OBF__aa, V_OBF__ll:$int, V_OBF__kkcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__kkbb:$int, V_OBF__kk:
  set(tuple2($int, $int)), V_OBF__jjcc:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__jjbb:$int, V_OBF__jj:
  $int, V_OBF__iicc:$int, V_OBF__iibb:$int, V_OBF__ii:$int, V_OBF__hhcc:$int,
  V_OBF__hhbb:$int, V_OBF__ggcc:$int, V_OBF__ggbb:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__ffcc:$int, V_OBF__ffbb:$int,
  V_OBF__eecc:set(tuple2($int, $int)), V_OBF__eebb:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:$int, V_OBF__cccc:
  set(tuple2($int, $int)), V_OBF__ccbb:$int, V_OBF__bbcc:
  set(tuple2($int, $int)), V_OBF__bbbb:set(tuple2($int, $int)), V_OBF__aacc:
  $int, V_OBF__aabb:$int]: ((f1(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc,
  V_OBF__ffbb, V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc,
  V_OBF__aabb) & (f13(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb, V_OBF__yy,
  V_OBF__xxbb, V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb, V_OBF__vv,
  V_OBF__uubb, V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb, V_OBF__ss,
  V_OBF__rrbb, V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq, V_OBF__ppcc,
  V_OBF__ppbb, V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm, V_OBF__llcc,
  V_OBF__llbb, V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk, V_OBF__jjcc,
  V_OBF__jjbb, V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb, V_OBF__cccc,
  V_OBF__ccbb, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc, V_OBF__aabb)
  & (f30(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb, V_OBF__yy, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb, V_OBF__vv, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb, V_OBF__ss, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc, V_OBF__ffbb, V_OBF__eecc,
  V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc, V_OBF__aabb) & ($true & $true))))
  => (f43(V_OBF__zzbb, V_OBF__zz, V_OBF__yybb, V_OBF__yy, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwbb, V_OBF__ww, V_OBF__vvbb, V_OBF__vv, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttbb, V_OBF__tt, V_OBF__ssbb, V_OBF__ss, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__pp, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__nn, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__jj, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffcc, V_OBF__ffbb, V_OBF__eecc,
  V_OBF__eebb, V_OBF__ddcc, V_OBF__ddbb, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbcc, V_OBF__bbbb, V_OBF__aacc, V_OBF__aabb) & $true))).
