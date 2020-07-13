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

tff(f1, type, f1: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f1_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f1(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem(set(tuple2($int, $int)), V_OBF__yydd, relation($int,
  $int, V_OBF__aabb, V_OBF__eebb)))
  & mem(set(tuple2($int, $int)), V_OBF__zzdd, relation($int,
  $int, V_OBF__aabb, V_OBF__eebb)))
  & mem(set(tuple2($int, $int)), V_OBF__aaee, relation($int,
  $int, V_OBF__aabb, V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__bbee,
  relation($int, $int, V_OBF__aabb, V_OBF__bbbb)))
  & mem(set($int), V_OBF__ccee, power($int, V_OBF__aabb)))
  & infix_eqeq(tuple2($int, $int), V_OBF__ddee, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccee, direct_product($int, $int,
  tuple2($int, $int), V_OBF__bbee, direct_product($int, $int,
  $int, V_OBF__yydd, V_OBF__aaee)))), singleton($int, V_OBF__yy))))
  & infix_eqeq(tuple2($int, $int), V_OBF__eeee, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccee, direct_product($int, $int,
  tuple2($int, $int), V_OBF__bbee, direct_product($int, $int,
  $int, V_OBF__yydd, V_OBF__aaee)))), singleton($int, V_OBF__zz))))
  & infix_eqeq(tuple2($int, $int), V_OBF__iidd, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccee, direct_product($int, $int,
  tuple2($int, $int), V_OBF__bbee, direct_product($int, $int,
  $int, V_OBF__yydd, V_OBF__aaee)))), singleton($int, V_OBF__vv))))
  & infix_eqeq(tuple2($int, $int), V_OBF__hhdd, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ccee, direct_product($int, $int,
  tuple2($int, $int), V_OBF__bbee, direct_product($int, $int,
  $int, V_OBF__zzdd, V_OBF__aaee)))), singleton($int, V_OBF__vv))))
  & mem(set(tuple2($int, $int)), V_OBF__zzdd,
  power(tuple2($int, $int), V_OBF__yydd)))
  & mem(set(tuple2($int, $int)), V_OBF__aaee, infix_plmngt($int,
  $int, V_OBF__aabb, V_OBF__pp))) & infix_eqeq($int, dom($int,
  $int, V_OBF__aaee), V_OBF__aabb)) & mem(set($int), ran($int,
  $int, V_OBF__bbee),
  power($int, union($int, union($int, singleton($int, V_OBF__yy),
  singleton($int, V_OBF__zz)), singleton($int, V_OBF__vv)))))
  & mem(set($int), V_OBF__aabb, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__aabb, empty($int))) & $true)
  & mem(set(tuple2($int, $int)), V_OBF__iidd, relation($int,
  $int, V_OBF__eebb, V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__hhdd,
  relation($int, $int, V_OBF__eebb, V_OBF__pp)))
  & mem(set($int), V_OBF__jjdd, power($int, V_OBF__pp)))
  & infix_eqeq(tuple2($int, $int), V_OBF__ffee, times($int,
  $int, diff($int, dom($int, $int, V_OBF__iidd), dom($int,
  tuple2($int, $int), range_substraction($int,
  tuple2($int, $int), direct_product($int, $int, $int, V_OBF__iidd,
  V_OBF__iidd), id($int, V_OBF__pp)))), V_OBF__pp)))
  & mem(set(tuple2($int, $int)), V_OBF__hhdd,
  power(tuple2($int, $int), V_OBF__iidd))) & mem($int, V_OBF__mmbb,
  V_OBF__pp)) & mem(set(tuple2($int, $int)), V_OBF__ddee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__eeee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp)))) & ~
  (V_OBF__mmbb = V_OBF__kkbb)) & infix_eqeq(tuple2($int, $int), V_OBF__ggee,
  union(tuple2($int, $int), V_OBF__ddee, semicolon($int, $int,
  $int, V_OBF__ddee, times($int, $int, singleton($int, V_OBF__mmbb),
  V_OBF__pp))))) & infix_eqeq(tuple2($int, $int), V_OBF__hhee,
  union(tuple2($int, $int), V_OBF__eeee, semicolon($int, $int,
  $int, V_OBF__eeee, times($int, $int, singleton($int, V_OBF__mmbb),
  V_OBF__pp))))) & mem($int, V_OBF__ppcc, V_OBF__oocc))
  & mem($int, V_OBF__kkbb, V_OBF__pp)) & mem(set($int), V_OBF__nn,
  power($int, V_OBF__eebb))) & mem(set($int), V_OBF__qqbb,
  power($int, V_OBF__eebb))) & mem(set($int), V_OBF__hhbb,
  power($int, V_OBF__eebb))) & mem(set($int), V_OBF__iicc,
  power($int, V_OBF__eebb))) & mem($int, V_OBF__jjcc, V_OBF__eebb))
  & mem($int, V_OBF__kkcc, V_OBF__eebb)) & mem($int, V_OBF__llcc,
  V_OBF__eebb)) & mem($int, V_OBF__mmcc, V_OBF__eebb))
  & mem(set(tuple2($int, $int)), V_OBF__ggee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__hhee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__ffee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set($int), V_OBF__iiee, power($int, V_OBF__pp)))
  & mem(set($int), V_OBF__qqbb, power($int, V_OBF__nn)))
  & mem(set($int), V_OBF__hhbb, power($int, diff($int, V_OBF__eebb,
  V_OBF__nn)))) & mem(set($int), V_OBF__iicc,
  power($int, diff($int, V_OBF__eebb, union($int, V_OBF__nn, V_OBF__hhbb)))))
  & ~ mem($int, V_OBF__jjcc, V_OBF__nn)) & ~ mem($int, V_OBF__jjcc,
  V_OBF__hhbb)) & ~ mem($int, V_OBF__jjcc, V_OBF__iicc)) & ~
  (V_OBF__jjcc = V_OBF__kkcc)) & ~ (V_OBF__jjcc = V_OBF__llcc)) & ~
  (V_OBF__jjcc = V_OBF__mmcc)) & ~ mem($int, V_OBF__kkcc, V_OBF__nn)) & ~
  mem($int, V_OBF__kkcc, V_OBF__hhbb)) & ~ mem($int, V_OBF__kkcc,
  V_OBF__iicc)) & ~ (V_OBF__kkcc = V_OBF__jjcc)) & ~
  (V_OBF__kkcc = V_OBF__llcc)) & ~ (V_OBF__kkcc = V_OBF__mmcc)) & ~
  mem($int, V_OBF__llcc, V_OBF__nn)) & ~ mem($int, V_OBF__llcc, V_OBF__hhbb))
  & ~ mem($int, V_OBF__llcc, V_OBF__iicc)) & ~ (V_OBF__llcc = V_OBF__jjcc))
  & ~ (V_OBF__llcc = V_OBF__kkcc)) & ~ (V_OBF__llcc = V_OBF__mmcc)) & ~
  mem($int, V_OBF__mmcc, V_OBF__nn)) & ~ mem($int, V_OBF__mmcc, V_OBF__hhbb))
  & ~ mem($int, V_OBF__mmcc, V_OBF__iicc)) & ~ (V_OBF__mmcc = V_OBF__jjcc))
  & ~ (V_OBF__mmcc = V_OBF__kkcc)) & ~ (V_OBF__mmcc = V_OBF__llcc))
  & infix_eqeq($int, V_OBF__eebb,
  union($int, union($int, union($int, V_OBF__nn, V_OBF__hhbb), V_OBF__iicc),
  union($int, union($int, union($int, singleton($int, V_OBF__jjcc),
  singleton($int, V_OBF__kkcc)), singleton($int, V_OBF__llcc)),
  singleton($int, V_OBF__mmcc)))))
  & infix_eqeq(tuple2($int, $int), V_OBF__jjee,
  union(tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int,
                                                            $int), union(
  tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int, $int), domain_restriction($int,
  $int, V_OBF__nn, V_OBF__ggee), times($int, $int, V_OBF__iicc,
  V_OBF__iiee)), times($int, $int, union($int, singleton($int, V_OBF__jjcc),
  singleton($int, V_OBF__kkcc)), V_OBF__iiee)), times($int,
  $int, V_OBF__hhbb, singleton($int, V_OBF__kkbb))), times($int,
  $int, V_OBF__qqbb, V_OBF__pp)), times($int,
  $int, singleton($int, V_OBF__llcc), V_OBF__pp)),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__mmcc,
  V_OBF__kkbb)))))
  & infix_eqeq(tuple2(tuple2($int, $int), $int), V_OBF__kkee,
  union(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, union(tuple2($int, $int), union(tuple2($int, $int), domain_restriction($int,
  $int, V_OBF__nn, V_OBF__hhee), times($int, $int, V_OBF__iicc,
  V_OBF__iiee)), singleton(tuple2($int, $int), tuple21($int,
  $int, V_OBF__mmcc, V_OBF__kkbb))), V_OBF__oocc), times(tuple2($int, $int),
  $int, times($int, $int, union($int, singleton($int, V_OBF__jjcc),
  singleton($int, V_OBF__kkcc)), V_OBF__iiee),
  singleton($int, V_OBF__ppcc)))))
  & infix_eqeq(tuple2($int, $int), V_OBF__llee, domain_restriction($int,
  $int, V_OBF__nn, V_OBF__ffee))) & mem($int, V_OBF__wwcc, integer))
  & infix_eqeq(tuple2($int, $int), V_OBF__mmee, times($int,
  $int, V_OBF__eebb, V_OBF__pp)))
  & infix_eqeq(tuple2($int, $int), V_OBF__nnee, times($int,
  $int, V_OBF__eebb, V_OBF__pp))) & $lesseq(1,V_OBF__wwcc))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ooee,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ppee,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqee,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rree,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd,
  power(tuple2(tuple2($int, enum_OBF__aa), $int), times(tuple2($int,
                                                        enum_OBF__aa),
  $int, times($int, enum_OBF__aa, integer, set_enum_OBF__aa), integer))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__ooee,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 0),
  union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__bb),
  singleton(enum_OBF__aa, e_OBF__ff)), singleton(enum_OBF__aa, e_OBF__gg)),
  singleton(enum_OBF__aa, e_OBF__ee)), singleton(enum_OBF__aa, e_OBF__cc))),
  singleton($int, 0))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__ppee,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 0),
  union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__hh),
  singleton(enum_OBF__aa, e_OBF__dd))), singleton($int, 1))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__qqee,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 1), singleton(enum_OBF__aa, e_OBF__cc)),
  singleton($int, 0))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__rree,
  times(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, singleton($int, 1),
  union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, union(enum_OBF__aa, singleton(enum_OBF__aa, e_OBF__bb),
  singleton(enum_OBF__aa, e_OBF__ff)), singleton(enum_OBF__aa, e_OBF__gg)),
  singleton(enum_OBF__aa, e_OBF__ee)), singleton(enum_OBF__aa, e_OBF__hh)),
  singleton(enum_OBF__aa, e_OBF__dd))), singleton($int, 1))))
  & infix_eqeq(tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__aadd,
  union(tuple2(tuple2($int, enum_OBF__aa), $int), union(tuple2(tuple2($int,
                                                               enum_OBF__aa),
                                                        $int), union(
  tuple2(tuple2($int, enum_OBF__aa), $int), V_OBF__ooee, V_OBF__ppee),
  V_OBF__qqee), V_OBF__rree))) & $true) & $true)
  & mem(set(tuple2($int, $int)), V_OBF__jjee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__kkee,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__eebb, V_OBF__pp), V_OBF__oocc))))
  & mem(set(tuple2($int, $int)), V_OBF__llee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__mmee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__nnee,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__ssee,
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
  $int, times(tuple2($int, $int), $int, V_OBF__jjee, V_OBF__oocc),
  singleton($int, V_OBF__yy)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__kkee, singleton($int, V_OBF__zz))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__llee, V_OBF__oocc), singleton($int, V_OBF__vv))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__mmee, V_OBF__oocc), singleton($int, V_OBF__ccdd))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__nnee, V_OBF__oocc), singleton($int, V_OBF__dddd))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__eebb, V_OBF__pp), V_OBF__oocc),
  singleton($int, V_OBF__eedd)))))
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssee,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__eebb,
  V_OBF__pp), V_OBF__oocc), V_OBF__bbbb)))) & mem($int, V_OBF__yy,
  V_OBF__bbbb)) & mem($int, V_OBF__zz, V_OBF__bbbb)) & mem($int, V_OBF__vv,
  V_OBF__bbbb)) & mem($int, V_OBF__ccdd, V_OBF__bbbb))
  & mem($int, V_OBF__dddd, V_OBF__bbbb)) & mem($int, V_OBF__eedd,
  V_OBF__bbbb)) & ~ (V_OBF__yy = V_OBF__zz)) & ~ (V_OBF__yy = V_OBF__vv)) & ~
  (V_OBF__yy = V_OBF__ccdd)) & ~ (V_OBF__yy = V_OBF__dddd)) & ~
  (V_OBF__yy = V_OBF__eedd)) & ~ (V_OBF__zz = V_OBF__yy)) & ~
  (V_OBF__zz = V_OBF__vv)) & ~ (V_OBF__zz = V_OBF__ccdd)) & ~
  (V_OBF__zz = V_OBF__dddd)) & ~ (V_OBF__zz = V_OBF__eedd)) & ~
  (V_OBF__vv = V_OBF__yy)) & ~ (V_OBF__vv = V_OBF__zz)) & ~
  (V_OBF__vv = V_OBF__ccdd)) & ~ (V_OBF__vv = V_OBF__dddd)) & ~
  (V_OBF__vv = V_OBF__eedd)) & ~ (V_OBF__ccdd = V_OBF__yy)) & ~
  (V_OBF__ccdd = V_OBF__zz)) & ~ (V_OBF__ccdd = V_OBF__vv)) & ~
  (V_OBF__ccdd = V_OBF__dddd)) & ~ (V_OBF__ccdd = V_OBF__eedd)) & ~
  (V_OBF__dddd = V_OBF__yy)) & ~ (V_OBF__dddd = V_OBF__zz)) & ~
  (V_OBF__dddd = V_OBF__vv)) & ~ (V_OBF__dddd = V_OBF__ccdd)) & ~
  (V_OBF__dddd = V_OBF__eedd)) & ~ (V_OBF__eedd = V_OBF__yy)) & ~
  (V_OBF__eedd = V_OBF__zz)) & ~ (V_OBF__eedd = V_OBF__vv)) & ~
  (V_OBF__eedd = V_OBF__ccdd)) & ~ (V_OBF__eedd = V_OBF__dddd))
  & mem(set($int), V_OBF__eebb, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__eebb, empty($int))) & mem(set($int), V_OBF__pp,
  finite_subsets($int, integer))) & ~ infix_eqeq($int, V_OBF__pp,
  empty($int))) & mem(set($int), V_OBF__oocc, finite_subsets($int, integer)))
  & ~ infix_eqeq($int, V_OBF__oocc, empty($int)))
  & mem(set($int), V_OBF__bbbb, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_OBF__bbbb, empty($int))))).

tff(f2, type, f2: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f2_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f2(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem(set(tuple2($int, $int)), V_OBF__kk, relation($int, $int, V_OBF__eebb,
  V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__ii, relation($int,
  $int, V_OBF__eebb, V_OBF__pp))) & mem(set($int), V_OBF__ll,
  power($int, V_OBF__pp))) & infix_eqeq(tuple2($int, $int), V_OBF__ddcc,
  times($int, $int, diff($int, dom($int,
  $int, union(tuple2($int, $int), V_OBF__ii, range_substraction($int,
  $int, V_OBF__kk, image($int, $int, times($int, $int, singleton($int, 0),
  diff($int, V_OBF__ll, singleton($int, V_OBF__rr))),
  singleton($int, V_OBF__mm))))), dom($int,
  tuple2($int, $int), range_substraction($int,
  tuple2($int, $int), direct_product($int, $int, $int, V_OBF__kk, V_OBF__kk),
  id($int, V_OBF__pp)))), V_OBF__pp)))
  & mem(set(tuple2($int, $int)), V_OBF__ii,
  power(tuple2($int, $int), V_OBF__kk)))
  & mem(set(tuple2($int, $int)), V_OBF__ppbb,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__nnbb,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & infix_eqeq(tuple2($int, $int), V_OBF__eecc,
  union(tuple2($int, $int), V_OBF__ppbb, semicolon($int, $int,
  $int, V_OBF__ppbb, times($int, $int, singleton($int, V_OBF__mmbb),
  V_OBF__pp))))) & infix_eqeq(tuple2($int, $int), V_OBF__ffcc,
  union(tuple2($int, $int), V_OBF__nnbb, semicolon($int, $int,
  $int, V_OBF__nnbb, times($int, $int, singleton($int, V_OBF__mmbb),
  V_OBF__pp))))) & mem(set(tuple2($int, $int)), V_OBF__eecc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__ffcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__ddcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & $true) & mem(set($int), V_OBF__ggcc, power($int, V_OBF__pp)))
  & infix_eqeq(tuple2($int, $int), V_OBF__hhcc,
  union(tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int,
                                                            $int), union(
  tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int, $int), domain_restriction($int,
  $int, V_OBF__nn, V_OBF__eecc), times($int, $int, V_OBF__iicc,
  V_OBF__ggcc)), times($int, $int, union($int, singleton($int, V_OBF__jjcc),
  singleton($int, V_OBF__kkcc)), V_OBF__ggcc)), times($int,
  $int, V_OBF__hhbb, singleton($int, V_OBF__kkbb))), dom(tuple2($int, $int),
  $int, range_restriction(tuple2($int, $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__qqbb, V_OBF__pp), singleton($int, 1)),
  singleton($int, V_OBF__mm)))), times($int,
  $int, singleton($int, V_OBF__llcc), V_OBF__pp)),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__mmcc,
  V_OBF__kkbb)))))
  & infix_eqeq(tuple2(tuple2($int, $int), $int), V_OBF__nncc,
  union(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, union(tuple2($int, $int), union(tuple2($int, $int), union(tuple2($int,
                                                                  $int), domain_restriction($int,
  $int, V_OBF__nn, V_OBF__ffcc), times($int, $int, V_OBF__iicc,
  V_OBF__ggcc)), dom(tuple2($int, $int),
  bool, range_restriction(tuple2($int, $int), bool, times(tuple2($int, $int),
  bool, times($int, $int, V_OBF__hhbb, singleton($int, V_OBF__kkbb)),
  singleton(bool, false)), singleton(bool, V_OBF__llbb)))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__mmcc,
  V_OBF__kkbb))), V_OBF__oocc), times(tuple2($int, $int), $int, times($int,
  $int, union($int, singleton($int, V_OBF__jjcc),
  singleton($int, V_OBF__kkcc)), V_OBF__ggcc),
  singleton($int, V_OBF__ppcc)))))
  & infix_eqeq(tuple2($int, $int), V_OBF__qqcc, domain_restriction($int,
  $int, V_OBF__nn, V_OBF__ddcc))) & mem($int, V_OBF__rrcc, V_OBF__pp))
  & mem($int, V_OBF__sscc, integer))
  & mem(set(tuple2($int, $int)), V_OBF__ttcc, relation($int, $int, integer,
  V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__uucc, relation($int,
  $int, integer, V_OBF__pp))) & infix_eqeq(tuple2($int, $int), V_OBF__vvcc,
  dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__wwcc, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__sscc,
  V_OBF__mm)))))) & infix_eqeq(tuple2($int, $int), V_OBF__xxcc,
  dom(tuple2($int, $int),
  tuple2($int, $int), range_substraction(tuple2($int, $int),
  tuple2($int, $int), times(tuple2($int, $int),
  tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp),
  singleton(tuple2($int, $int), tuple21($int, $int, 0, 0))),
  singleton(tuple2($int, $int), tuple21($int, $int, V_OBF__sscc,
  V_OBF__mm)))))) & mem($int, V_OBF__sscc, mk(0, V_OBF__wwcc)))
  & mem(set(tuple2($int, $int)), V_OBF__ttcc, infix_plmngt($int, $int, mk(1,
  V_OBF__wwcc), V_OBF__pp))) & infix_eqeq($int, dom($int, $int, V_OBF__ttcc),
  mk(1, V_OBF__wwcc))) & mem(set(tuple2($int, $int)), V_OBF__uucc,
  infix_plmngt($int, $int, mk(1, V_OBF__wwcc), V_OBF__pp)))
  & infix_eqeq($int, dom($int, $int, V_OBF__uucc), mk(1, V_OBF__wwcc)))
  & mem($int, V_OBF__yycc, integer)) & $true) & mem($int, V_OBF__mm,
  integer)) & mem(tuple2(tuple2($int, enum_OBF__aa), $int), tuple21($int,
  tuple2($int, enum_OBF__aa), tuple21(enum_OBF__aa, $int, V_OBF__yycc,
  V_OBF__zzcc), V_OBF__mm), V_OBF__aadd))
  & mem(set(tuple2($int, $int)), V_OBF__hhcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2(tuple2($int, $int), $int)), V_OBF__nncc,
  power(tuple2(tuple2($int, $int), $int), times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__eebb, V_OBF__pp), V_OBF__oocc))))
  & mem(set(tuple2($int, $int)), V_OBF__qqcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__vvcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & mem(set(tuple2($int, $int)), V_OBF__xxcc,
  power(tuple2($int, $int), times($int, $int, V_OBF__eebb, V_OBF__pp))))
  & infix_eqeq(tuple2(tuple2(tuple2($int, $int), $int), $int), V_OBF__bbdd,
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
  $int, times(tuple2($int, $int), $int, V_OBF__hhcc, V_OBF__oocc),
  singleton($int, V_OBF__yy)), times(tuple2(tuple2($int, $int), $int),
  $int, V_OBF__nncc, singleton($int, V_OBF__zz))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__qqcc, V_OBF__oocc), singleton($int, V_OBF__vv))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__vvcc, V_OBF__oocc), singleton($int, V_OBF__ccdd))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, V_OBF__xxcc, V_OBF__oocc), singleton($int, V_OBF__dddd))),
  times(tuple2(tuple2($int, $int), $int), $int, times(tuple2($int, $int),
  $int, times($int, $int, V_OBF__eebb, V_OBF__pp), V_OBF__oocc),
  singleton($int, V_OBF__eedd))))) & mem($int, V_OBF__tt, integer))
  & mem($int, V_OBF__jj, V_OBF__eebb)) & mem($int, V_OBF__rr, V_OBF__pp))
  & mem($int, V_OBF__ffdd, V_OBF__oocc)) & mem($int, V_OBF__uu, V_OBF__bbbb))
  & $true)
  & mem(set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbdd,
  power(tuple2(tuple2(tuple2($int, $int), $int), $int), times(tuple2(
                                                              tuple2($int,
                                                              $int), $int),
  $int, times(tuple2($int, $int), $int, times($int, $int, V_OBF__eebb,
  V_OBF__pp), V_OBF__oocc), V_OBF__bbbb)))) & $true)
  & infix_eqeq(tuple2($int, $int), union(tuple2($int, $int), V_OBF__ii,
  range_substraction($int, $int, V_OBF__kk, image($int, $int, times($int,
  $int, singleton($int, 0), diff($int, V_OBF__ll,
  singleton($int, V_OBF__rr))), singleton($int, 1)))), V_OBF__kk))
  & infix_eqeq(tuple2($int, $int), union(tuple2($int, $int), V_OBF__ii,
  range_substraction($int, $int, V_OBF__kk, image($int, $int, times($int,
  $int, singleton($int, 0), diff($int, V_OBF__ll,
  singleton($int, V_OBF__rr))), singleton($int, 0)))),
  union(tuple2($int, $int), V_OBF__ii, range_substraction($int,
  $int, V_OBF__kk, diff($int, V_OBF__ll, singleton($int, V_OBF__rr))))))
  & infix_eqeq(tuple2($int, $int), union(tuple2($int, $int), V_OBF__hhdd,
  range_substraction($int, $int, V_OBF__iidd, image($int, $int, times($int,
  $int, singleton($int, 0), diff($int, V_OBF__jjdd,
  singleton($int, V_OBF__kkbb))), singleton($int, 1)))), V_OBF__iidd))
  & mem($int, V_OBF__mm, union($int, singleton($int, 0),
  singleton($int, 1))))
  & mem(set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aadd,
  infix_plmngt(tuple2($int, enum_OBF__aa), $int, times($int,
  enum_OBF__aa, union($int, singleton($int, 0), singleton($int, 1)),
  set_enum_OBF__aa), union($int, singleton($int, 0), singleton($int, 1)))))
  & infix_eqeq(tuple2($int, enum_OBF__aa), dom(tuple2($int, enum_OBF__aa),
  $int, V_OBF__aadd), times($int,
  enum_OBF__aa, union($int, singleton($int, 0), singleton($int, 1)),
  set_enum_OBF__aa))) & $true) & mem(set(tuple2($int, $int)), V_OBF__ttbb,
  relation($int, $int, V_OBF__aabb, V_OBF__eebb)))
  & mem(set(tuple2($int, $int)), V_OBF__aacc, relation($int,
  $int, V_OBF__aabb, V_OBF__eebb)))
  & mem(set(tuple2($int, $int)), V_OBF__vvbb, relation($int,
  $int, V_OBF__aabb, V_OBF__pp))) & mem(set(tuple2($int, $int)), V_OBF__uubb,
  relation($int, $int, V_OBF__aabb, V_OBF__bbbb)))
  & mem(set($int), V_OBF__ssbb, power($int, V_OBF__aabb)))
  & mem(set($int), V_OBF__cccc, power($int, V_OBF__aabb)))
  & mem(set($int), V_OBF__bbcc, power($int, V_OBF__aabb)))
  & mem(set($int), V_OBF__qq, power($int, V_OBF__pp)))
  & mem(set($int), V_OBF__ss, power($int, V_OBF__aabb)))
  & mem(set($int), V_OBF__oobb, power($int, V_OBF__aabb)))
  & infix_eqeq(tuple2($int, $int), V_OBF__ppbb, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ssbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__uubb, direct_product($int, $int,
  $int, V_OBF__ttbb, V_OBF__vvbb)))), singleton($int, V_OBF__yy))))
  & infix_eqeq(tuple2($int, $int), V_OBF__nnbb, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ssbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__uubb, direct_product($int, $int,
  $int, V_OBF__ttbb, V_OBF__vvbb)))), singleton($int, V_OBF__zz))))
  & infix_eqeq(tuple2($int, $int), V_OBF__kk, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ssbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__uubb, direct_product($int, $int,
  $int, V_OBF__ttbb, V_OBF__vvbb)))), singleton($int, V_OBF__vv))))
  & infix_eqeq(tuple2($int, $int), V_OBF__ii, image($int,
  tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ssbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__uubb, direct_product($int, $int,
  $int, V_OBF__aacc, V_OBF__vvbb)))), singleton($int, V_OBF__vv))))
  & mem(set(tuple2($int, $int)), V_OBF__aacc,
  power(tuple2($int, $int), V_OBF__ttbb)))
  & mem(set(tuple2($int, $int)), V_OBF__vvbb, infix_plmngt($int,
  $int, V_OBF__aabb, V_OBF__pp))) & infix_eqeq($int, dom($int,
  $int, V_OBF__vvbb), V_OBF__aabb)) & mem(set($int), ran($int,
  $int, V_OBF__uubb),
  power($int, union($int, union($int, singleton($int, V_OBF__yy),
  singleton($int, V_OBF__zz)), singleton($int, V_OBF__vv)))))
  & ((V_OBF__tt = 2) => infix_eqeq($int, V_OBF__cccc,
  inter($int, V_OBF__ssbb, image($int, $int, inverse($int,
  $int, V_OBF__ttbb), singleton($int, V_OBF__jj)))))) & ((V_OBF__tt = 2)
  => infix_eqeq($int, V_OBF__bbcc, inter($int, inter($int, V_OBF__ssbb,
  image($int, $int, inverse($int, $int, V_OBF__ttbb),
  singleton($int, V_OBF__jj))), image($int, $int, inverse($int,
  $int, V_OBF__uubb), singleton($int, V_OBF__uu)))))) & ((V_OBF__tt = 2)
  => infix_eqeq($int, V_OBF__qq, image($int, $int, V_OBF__vvbb,
  V_OBF__bbcc)))) & ((V_OBF__tt = 2) => infix_eqeq($int, V_OBF__ss,
  inter($int, inter($int, V_OBF__ssbb, image($int, $int, inverse($int,
  $int, V_OBF__aacc), singleton($int, V_OBF__jj))), image($int,
  $int, inverse($int, $int, V_OBF__uubb), singleton($int, V_OBF__uu))))))
  & ((V_OBF__tt = 2) => infix_eqeq($int, V_OBF__oobb,
  inter($int, inter($int, inter($int, V_OBF__ssbb, image($int,
  $int, inverse($int, $int, V_OBF__ttbb), singleton($int, V_OBF__jj))),
  image($int, $int, inverse($int, $int, V_OBF__uubb),
  singleton($int, V_OBF__uu))), image($int, $int, inverse($int,
  $int, V_OBF__vvbb), union($int, singleton($int, V_OBF__rr),
  singleton($int, V_OBF__mmbb))))))) & (V_OBF__kkdd = V_OBF__tt))
  & (V_OBF__lldd = V_OBF__jj)) & (V_OBF__mmdd = V_OBF__rr))
  & (V_OBF__nndd = V_OBF__ffdd)) & (V_OBF__oodd = V_OBF__uu))
  & (V_OBF__ppdd = V_OBF__ggdd)) & (V_OBF__qqdd = V_OBF__mm))
  & (V_OBF__rrdd = V_OBF__rrcc)) & (V_OBF__ssdd = V_OBF__sscc))
  & infix_eqeq(tuple2($int, $int), V_OBF__ttdd, V_OBF__ttcc))
  & infix_eqeq(tuple2($int, $int), V_OBF__uudd, V_OBF__uucc))
  & (V_OBF__vvdd = V_OBF__llbb)) & infix_eqeq($int, V_OBF__wwdd,
  V_OBF__ggcc)) & infix_eqeq($int, V_OBF__xxdd, V_OBF__ll)))).

tff(f9, type, f9: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f9_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f9(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> ((($true & (((V_OBF__tt = 2) & (V_OBF__uu = V_OBF__vv))
  => infix_eqeq($int, V_OBF__qq, image($int, $int, V_OBF__kk,
  singleton($int, V_OBF__jj))))) & (((V_OBF__tt = 2)
  & (V_OBF__uu = V_OBF__vv)) => infix_eqeq($int, image($int,
  $int, V_OBF__vvbb, V_OBF__ss), image($int, $int, V_OBF__ii,
  singleton($int, V_OBF__jj))))) & (V_OBF__tt = 2)))).

tff(f11, type, f11: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f11_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f11(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> infix_eqeq($int, V_OBF__bbcc, inter($int, V_OBF__cccc, image($int,
  $int, inverse($int, $int, V_OBF__uubb), singleton($int, V_OBF__uu)))))).

tff(f12, type, f12: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f12_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f12(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> ((($true & (((V_OBF__tt = 2) & (V_OBF__uu = V_OBF__vv))
  => infix_eqeq($int, V_OBF__qq, image($int, $int, V_OBF__kk,
  singleton($int, V_OBF__jj))))) & (((V_OBF__tt = 2)
  & (V_OBF__uu = V_OBF__vv)) => infix_eqeq($int, image($int,
  $int, V_OBF__vvbb, V_OBF__ss), image($int, $int, V_OBF__ii,
  singleton($int, V_OBF__jj))))) & ((V_OBF__tt = 2)
  => infix_eqeq($int, V_OBF__bbcc, inter($int, V_OBF__cccc, image($int,
  $int, inverse($int, $int, V_OBF__uubb), singleton($int, V_OBF__uu)))))))).

tff(f13, type, f13: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f13_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f13(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> (((((($true & infix_eqeq($int, V_OBF__rrbb, inter($int, V_OBF__wwbb,
  image($int, $int, inverse($int, $int, V_OBF__vvbb),
  union($int, singleton($int, V_OBF__rr), singleton($int, V_OBF__mmbb))))))
  & (V_OBF__tt = 1)) & infix_eqeq($int, V_OBF__zzbb, inter($int, V_OBF__ssbb,
  image($int, $int, inverse($int, $int, V_OBF__ttbb),
  singleton($int, V_OBF__jj))))) & infix_eqeq($int, V_OBF__wwbb,
  inter($int, V_OBF__zzbb, image($int, $int, inverse($int,
  $int, V_OBF__uubb), singleton($int, V_OBF__uu)))))
  & infix_eqeq($int, V_OBF__yybb, image($int, $int, V_OBF__vvbb,
  V_OBF__wwbb))) & infix_eqeq($int, V_OBF__xxbb,
  inter($int, inter($int, V_OBF__ssbb, image($int, $int, inverse($int,
  $int, V_OBF__aacc), singleton($int, V_OBF__jj))), image($int,
  $int, inverse($int, $int, V_OBF__uubb), singleton($int, V_OBF__uu))))))).

tff(f15, type, f15: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f15_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f15(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set($int), V_OBF__zzbb, power($int, V_OBF__aabb)))).

tff(f17, type, f17: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f17_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f17(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set($int), V_OBF__wwbb, power($int, V_OBF__aabb)))).

tff(f19, type, f19: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f19_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f19(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set($int), V_OBF__yybb, power($int, V_OBF__pp)))).

tff(f21, type, f21: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f21_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f21(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set($int), V_OBF__xxbb, power($int, V_OBF__aabb)))).

tff(f25, type, f25: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f25_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f25(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> infix_eqeq($int, V_OBF__wwbb, inter($int, inter($int, V_OBF__ssbb,
  image($int, $int, inverse($int, $int, V_OBF__ttbb),
  singleton($int, V_OBF__jj))), image($int, $int, inverse($int,
  $int, V_OBF__uubb), singleton($int, V_OBF__uu)))))).

tff(f27, type, f27: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f27_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f27(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> infix_eqeq($int, V_OBF__rrbb,
  inter($int, inter($int, inter($int, V_OBF__ssbb, image($int,
  $int, inverse($int, $int, V_OBF__ttbb), singleton($int, V_OBF__jj))),
  image($int, $int, inverse($int, $int, V_OBF__uubb),
  singleton($int, V_OBF__uu))), image($int, $int, inverse($int,
  $int, V_OBF__vvbb), union($int, singleton($int, V_OBF__rr),
  singleton($int, V_OBF__mmbb))))))).

tff(f40, type, f40: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f40_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f40(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> ((((((((((((($true & mem($int, V_OBF__jj, V_OBF__hhbb))
  & mem(set($int), V_OBF__iibb, power($int, V_OBF__pp)))
  & mem(set($int), V_OBF__jjbb, power($int, V_OBF__pp)))
  & mem(set(tuple2($int, $int)), V_OBF__ggbb, relation($int,
  $int, V_OBF__aabb, V_OBF__eebb)))
  & mem(set(tuple2($int, $int)), V_OBF__ddbb,
  power(tuple2($int, $int), V_OBF__ggbb)))
  & mem(set(tuple2($int, $int)), V_OBF__ccbb, infix_plmngt($int,
  $int, V_OBF__aabb, V_OBF__pp))) & infix_eqeq($int, dom($int,
  $int, V_OBF__ccbb), V_OBF__aabb)) & mem(set(tuple2($int, $int)), V_OBF__xx,
  relation($int, $int, V_OBF__aabb,
  union($int, union($int, singleton($int, V_OBF__yy),
  singleton($int, V_OBF__zz)), singleton($int, V_OBF__vv)))))
  & mem(set($int), V_OBF__ffbb, power($int, V_OBF__aabb))) & (V_OBF__tt = 2))
  & (V_OBF__uu = V_OBF__zz)) & (V_OBF__rr = V_OBF__kkbb))
  & (V_OBF__llbb = false)))).

tff(f41, type, f41: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f41_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f41(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set(tuple2($int, $int)), image($int, tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ffbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__xx, direct_product($int, $int,
  $int, V_OBF__ggbb, V_OBF__ccbb)))), singleton($int, V_OBF__yy)),
  relation($int, $int, V_OBF__eebb, V_OBF__pp)))).

tff(f42, type, f42: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f42_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f42(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set(tuple2($int, $int)), image($int, tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ffbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__xx, direct_product($int, $int,
  $int, V_OBF__ggbb, V_OBF__ccbb)))), singleton($int, V_OBF__zz)),
  relation($int, $int, V_OBF__eebb, V_OBF__pp)))).

tff(f43, type, f43: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f43_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f43(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set(tuple2($int, $int)), image($int, tuple2($int, $int), ran($int,
  tuple2($int, tuple2($int, $int)), domain_restriction($int,
  tuple2($int, tuple2($int, $int)), V_OBF__ffbb, direct_product($int, $int,
  tuple2($int, $int), V_OBF__xx, direct_product($int, $int,
  $int, V_OBF__ggbb, V_OBF__ccbb)))), singleton($int, V_OBF__vv)),
  relation($int, $int, V_OBF__eebb, V_OBF__pp)))).

tff(f48, type, f48: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f48_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f48(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set(tuple2($int, $int)), V_OBF__ccbb, relation($int,
  $int, V_OBF__aabb, V_OBF__pp)))).

tff(f52, type, f52: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f52_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f52(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem(set($int), ran($int, $int, V_OBF__xx),
  power($int, union($int, union($int, singleton($int, V_OBF__yy),
  singleton($int, V_OBF__zz)), singleton($int, V_OBF__vv)))))).

tff(f53, type, f53: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f53_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f53(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> (((((($true & mem($int, V_OBF__jj, V_OBF__nn)) & mem($int, V_OBF__rr,
  V_OBF__qq)) & mem($int, V_OBF__oo, V_OBF__pp)) & (V_OBF__tt = 2))
  & (V_OBF__uu = V_OBF__vv)) & infix_eqeq($int, V_OBF__qq,
  singleton($int, V_OBF__oo))))).

tff(f55, type, f55: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f55_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f55(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem($int, V_OBF__rr, image($int, $int, V_OBF__kk,
  singleton($int, V_OBF__jj))))).

tff(f56, type, f56: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f56_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f56(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> (((((((($true & mem($int, V_OBF__jj, V_OBF__nn)) & ~
  mem($int, V_OBF__rr, V_OBF__qq)) & (((V_OBF__mm = 0)
  & mem(set($int), V_OBF__qq, power($int, V_OBF__ll))) => ~
  infix_eqeq($int, V_OBF__ss, empty($int)))) & mem($int, V_OBF__oo,
  V_OBF__pp)) & mem($int, V_OBF__ww, V_OBF__qq)) & (V_OBF__tt = 2))
  & (V_OBF__uu = V_OBF__vv)) & infix_eqeq($int, V_OBF__qq,
  singleton($int, V_OBF__oo))))).

tff(f57, type, f57: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f57_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f57(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb) <=> ~
  mem($int, V_OBF__rr, image($int, $int, V_OBF__kk,
  singleton($int, V_OBF__jj))))).

tff(f60, type, f60: (set(tuple2($int, $int)) * enum_OBF__aa * set($int) *
  $int * set(tuple2($int, $int)) * $int * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set($int) * set(tuple2($int, $int)) * set($int) *
  $int * set($int) * $int * bool * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * $int * $int *
  set($int) * set($int) * set(tuple2(tuple2($int, enum_OBF__aa), $int)) *
  $int * $int * set($int) * $int *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int *
  set(tuple2($int, $int)) * set($int) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * bool * $int *
  set(tuple2($int, $int)) * set($int) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * $int * set($int) *
  set($int) * $int * set(tuple2($int, $int)) * $int *
  set(tuple2(tuple2($int, $int), $int)) * set(tuple2($int, $int)) *
  set($int) * set(tuple2($int, $int)) * $int * $int * $int * $int *
  set(tuple2($int, $int)) * $int * $int * bool * set($int) *
  set(tuple2(tuple2($int, $int), $int)) * $int * $int * $int *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) * $int *
  set($int) * $int * set($int) * set(tuple2($int, $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * bool * set($int) * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) * set($int) *
  set(tuple2($int, $int)) * $int * set(tuple2($int, $int)) *
  set(tuple2($int, $int)) * set($int) * $int * set($int) *
  set(tuple2($int, $int)) * set(tuple2($int, $int)) *
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)) * set($int) *
  set($int) * set(tuple2($int, $int)) *
  set(tuple2(tuple2($int, enum_OBF__aa), $int)) * set(tuple2($int, $int)) *
  set($int)) > $o).

tff(f60_def, axiom, ![V_OBF__zzdd:set(tuple2($int, $int)), V_OBF__zzcc:
  enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int, V_OBF__yydd:
  set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:set($int),
  V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:set(tuple2($int, $int)),
  V_OBF__xxbb:set($int), V_OBF__xx:set(tuple2($int, $int)), V_OBF__wwdd:
  set($int), V_OBF__wwcc:$int, V_OBF__wwbb:set($int), V_OBF__ww:$int,
  V_OBF__vvdd:bool, V_OBF__vvcc:set(tuple2($int, $int)), V_OBF__vvbb:
  set(tuple2($int, $int)), V_OBF__vv:$int, V_OBF__uudd:
  set(tuple2($int, $int)), V_OBF__uucc:set(tuple2($int, $int)), V_OBF__uubb:
  set(tuple2($int, $int)), V_OBF__uu:$int, V_OBF__ttdd:
  set(tuple2($int, $int)), V_OBF__ttcc:set(tuple2($int, $int)), V_OBF__ttbb:
  set(tuple2($int, $int)), V_OBF__tt:$int, V_OBF__ssee:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__ssdd:$int,
  V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:set($int), V_OBF__rree:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__rrdd:$int,
  V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int, V_OBF__qqee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:$int,
  V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int), V_OBF__qq:
  set($int), V_OBF__ppee:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__ppdd:bool, V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)),
  V_OBF__pp:set($int), V_OBF__ooee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:$int,
  V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int, V_OBF__nnee:
  set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: (f60(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  <=> mem($int, V_OBF__ww, image($int, $int, V_OBF__kk,
  singleton($int, V_OBF__jj))))).

tff(oBF__zzee_6, conjecture, ![V_OBF__zzdd:set(tuple2($int, $int)),
  V_OBF__zzcc:enum_OBF__aa, V_OBF__zzbb:set($int), V_OBF__zz:$int,
  V_OBF__yydd:set(tuple2($int, $int)), V_OBF__yycc:$int, V_OBF__yybb:
  set($int), V_OBF__yy:$int, V_OBF__xxdd:set($int), V_OBF__xxcc:
  set(tuple2($int, $int)), V_OBF__xxbb:set($int), V_OBF__xx:
  set(tuple2($int, $int)), V_OBF__wwdd:set($int), V_OBF__wwcc:$int,
  V_OBF__wwbb:set($int), V_OBF__ww:$int, V_OBF__vvdd:bool, V_OBF__vvcc:
  set(tuple2($int, $int)), V_OBF__vvbb:set(tuple2($int, $int)), V_OBF__vv:
  $int, V_OBF__uudd:set(tuple2($int, $int)), V_OBF__uucc:
  set(tuple2($int, $int)), V_OBF__uubb:set(tuple2($int, $int)), V_OBF__uu:
  $int, V_OBF__ttdd:set(tuple2($int, $int)), V_OBF__ttcc:
  set(tuple2($int, $int)), V_OBF__ttbb:set(tuple2($int, $int)), V_OBF__tt:
  $int, V_OBF__ssee:set(tuple2(tuple2(tuple2($int, $int), $int), $int)),
  V_OBF__ssdd:$int, V_OBF__sscc:$int, V_OBF__ssbb:set($int), V_OBF__ss:
  set($int), V_OBF__rree:set(tuple2(tuple2($int, enum_OBF__aa), $int)),
  V_OBF__rrdd:$int, V_OBF__rrcc:$int, V_OBF__rrbb:set($int), V_OBF__rr:$int,
  V_OBF__qqee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__qqdd:
  $int, V_OBF__qqcc:set(tuple2($int, $int)), V_OBF__qqbb:set($int),
  V_OBF__qq:set($int), V_OBF__ppee:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__ppdd:bool,
  V_OBF__ppcc:$int, V_OBF__ppbb:set(tuple2($int, $int)), V_OBF__pp:set($int),
  V_OBF__ooee:set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__oodd:
  $int, V_OBF__oocc:set($int), V_OBF__oobb:set($int), V_OBF__oo:$int,
  V_OBF__nnee:set(tuple2($int, $int)), V_OBF__nndd:$int, V_OBF__nncc:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__nnbb:set(tuple2($int, $int)),
  V_OBF__nn:set($int), V_OBF__mmee:set(tuple2($int, $int)), V_OBF__mmdd:$int,
  V_OBF__mmcc:$int, V_OBF__mmbb:$int, V_OBF__mm:$int, V_OBF__llee:
  set(tuple2($int, $int)), V_OBF__lldd:$int, V_OBF__llcc:$int, V_OBF__llbb:
  bool, V_OBF__ll:set($int), V_OBF__kkee:
  set(tuple2(tuple2($int, $int), $int)), V_OBF__kkdd:$int, V_OBF__kkcc:$int,
  V_OBF__kkbb:$int, V_OBF__kk:set(tuple2($int, $int)), V_OBF__jjee:
  set(tuple2($int, $int)), V_OBF__jjdd:set($int), V_OBF__jjcc:$int,
  V_OBF__jjbb:set($int), V_OBF__jj:$int, V_OBF__iiee:set($int), V_OBF__iidd:
  set(tuple2($int, $int)), V_OBF__iicc:set($int), V_OBF__iibb:set($int),
  V_OBF__ii:set(tuple2($int, $int)), V_OBF__hhee:set(tuple2($int, $int)),
  V_OBF__hhdd:set(tuple2($int, $int)), V_OBF__hhcc:set(tuple2($int, $int)),
  V_OBF__hhbb:set($int), V_OBF__ggee:set(tuple2($int, $int)), V_OBF__ggdd:
  bool, V_OBF__ggcc:set($int), V_OBF__ggbb:set(tuple2($int, $int)),
  V_OBF__ffee:set(tuple2($int, $int)), V_OBF__ffdd:$int, V_OBF__ffcc:
  set(tuple2($int, $int)), V_OBF__ffbb:set($int), V_OBF__eeee:
  set(tuple2($int, $int)), V_OBF__eedd:$int, V_OBF__eecc:
  set(tuple2($int, $int)), V_OBF__eebb:set($int), V_OBF__ddee:
  set(tuple2($int, $int)), V_OBF__dddd:$int, V_OBF__ddcc:
  set(tuple2($int, $int)), V_OBF__ddbb:set(tuple2($int, $int)), V_OBF__ccee:
  set($int), V_OBF__ccdd:$int, V_OBF__cccc:set($int), V_OBF__ccbb:
  set(tuple2($int, $int)), V_OBF__bbee:set(tuple2($int, $int)), V_OBF__bbdd:
  set(tuple2(tuple2(tuple2($int, $int), $int), $int)), V_OBF__bbcc:set($int),
  V_OBF__bbbb:set($int), V_OBF__aaee:set(tuple2($int, $int)), V_OBF__aadd:
  set(tuple2(tuple2($int, enum_OBF__aa), $int)), V_OBF__aacc:
  set(tuple2($int, $int)), V_OBF__aabb:set($int)]: ((f1(V_OBF__zzdd,
  V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb,
  V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd,
  V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb,
  V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd,
  V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc,
  V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb,
  V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq,
  V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee,
  V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd,
  V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc,
  V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb,
  V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk,
  V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee,
  V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd,
  V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc,
  V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb,
  V_OBF__eeee, V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee,
  V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd,
  V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc,
  V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb)
  & (f2(V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd,
  V_OBF__yycc, V_OBF__yybb, V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd,
  V_OBF__vvcc, V_OBF__vvbb, V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee,
  V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd,
  V_OBF__rrcc, V_OBF__rrbb, V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__qq, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__pp, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee,
  V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__jj, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee,
  V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eeee, V_OBF__eedd, V_OBF__eecc,
  V_OBF__eebb, V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee,
  V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) & (f12(V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb,
  V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb, V_OBF__yy, V_OBF__xxdd,
  V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb,
  V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb, V_OBF__vv, V_OBF__uudd,
  V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb,
  V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb, V_OBF__ss,
  V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb, V_OBF__rr, V_OBF__qqee,
  V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq, V_OBF__ppee, V_OBF__ppdd,
  V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc,
  V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb,
  V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm,
  V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkee,
  V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk, V_OBF__jjee, V_OBF__jjdd,
  V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc,
  V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb,
  V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffee,
  V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb, V_OBF__eeee, V_OBF__eedd,
  V_OBF__eecc, V_OBF__eebb, V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc,
  V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb,
  V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aaee,
  V_OBF__aadd, V_OBF__aacc, V_OBF__aabb) & (f40(V_OBF__zzdd, V_OBF__zzcc,
  V_OBF__zzbb, V_OBF__zz, V_OBF__yydd, V_OBF__yycc, V_OBF__yybb, V_OBF__yy,
  V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb, V_OBF__xx, V_OBF__wwdd, V_OBF__wwcc,
  V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd, V_OBF__vvcc, V_OBF__vvbb, V_OBF__vv,
  V_OBF__uudd, V_OBF__uucc, V_OBF__uubb, V_OBF__uu, V_OBF__ttdd, V_OBF__ttcc,
  V_OBF__ttbb, V_OBF__tt, V_OBF__ssee, V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb,
  V_OBF__ss, V_OBF__rree, V_OBF__rrdd, V_OBF__rrcc, V_OBF__rrbb, V_OBF__rr,
  V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc, V_OBF__qqbb, V_OBF__qq, V_OBF__ppee,
  V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb, V_OBF__pp, V_OBF__ooee, V_OBF__oodd,
  V_OBF__oocc, V_OBF__oobb, V_OBF__oo, V_OBF__nnee, V_OBF__nndd, V_OBF__nncc,
  V_OBF__nnbb, V_OBF__nn, V_OBF__mmee, V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb,
  V_OBF__mm, V_OBF__llee, V_OBF__lldd, V_OBF__llcc, V_OBF__llbb, V_OBF__ll,
  V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc, V_OBF__kkbb, V_OBF__kk, V_OBF__jjee,
  V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb, V_OBF__jj, V_OBF__iiee, V_OBF__iidd,
  V_OBF__iicc, V_OBF__iibb, V_OBF__ii, V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc,
  V_OBF__hhbb, V_OBF__ggee, V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb,
  V_OBF__ffee, V_OBF__ffdd, V_OBF__ffcc, V_OBF__ffbb, V_OBF__eeee,
  V_OBF__eedd, V_OBF__eecc, V_OBF__eebb, V_OBF__ddee, V_OBF__dddd,
  V_OBF__ddcc, V_OBF__ddbb, V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc,
  V_OBF__ccbb, V_OBF__bbee, V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb,
  V_OBF__aaee, V_OBF__aadd, V_OBF__aacc, V_OBF__aabb) & ($true & $true)))))
  => (f48(V_OBF__zzdd, V_OBF__zzcc, V_OBF__zzbb, V_OBF__zz, V_OBF__yydd,
  V_OBF__yycc, V_OBF__yybb, V_OBF__yy, V_OBF__xxdd, V_OBF__xxcc, V_OBF__xxbb,
  V_OBF__xx, V_OBF__wwdd, V_OBF__wwcc, V_OBF__wwbb, V_OBF__ww, V_OBF__vvdd,
  V_OBF__vvcc, V_OBF__vvbb, V_OBF__vv, V_OBF__uudd, V_OBF__uucc, V_OBF__uubb,
  V_OBF__uu, V_OBF__ttdd, V_OBF__ttcc, V_OBF__ttbb, V_OBF__tt, V_OBF__ssee,
  V_OBF__ssdd, V_OBF__sscc, V_OBF__ssbb, V_OBF__ss, V_OBF__rree, V_OBF__rrdd,
  V_OBF__rrcc, V_OBF__rrbb, V_OBF__rr, V_OBF__qqee, V_OBF__qqdd, V_OBF__qqcc,
  V_OBF__qqbb, V_OBF__qq, V_OBF__ppee, V_OBF__ppdd, V_OBF__ppcc, V_OBF__ppbb,
  V_OBF__pp, V_OBF__ooee, V_OBF__oodd, V_OBF__oocc, V_OBF__oobb, V_OBF__oo,
  V_OBF__nnee, V_OBF__nndd, V_OBF__nncc, V_OBF__nnbb, V_OBF__nn, V_OBF__mmee,
  V_OBF__mmdd, V_OBF__mmcc, V_OBF__mmbb, V_OBF__mm, V_OBF__llee, V_OBF__lldd,
  V_OBF__llcc, V_OBF__llbb, V_OBF__ll, V_OBF__kkee, V_OBF__kkdd, V_OBF__kkcc,
  V_OBF__kkbb, V_OBF__kk, V_OBF__jjee, V_OBF__jjdd, V_OBF__jjcc, V_OBF__jjbb,
  V_OBF__jj, V_OBF__iiee, V_OBF__iidd, V_OBF__iicc, V_OBF__iibb, V_OBF__ii,
  V_OBF__hhee, V_OBF__hhdd, V_OBF__hhcc, V_OBF__hhbb, V_OBF__ggee,
  V_OBF__ggdd, V_OBF__ggcc, V_OBF__ggbb, V_OBF__ffee, V_OBF__ffdd,
  V_OBF__ffcc, V_OBF__ffbb, V_OBF__eeee, V_OBF__eedd, V_OBF__eecc,
  V_OBF__eebb, V_OBF__ddee, V_OBF__dddd, V_OBF__ddcc, V_OBF__ddbb,
  V_OBF__ccee, V_OBF__ccdd, V_OBF__cccc, V_OBF__ccbb, V_OBF__bbee,
  V_OBF__bbdd, V_OBF__bbcc, V_OBF__bbbb, V_OBF__aaee, V_OBF__aadd,
  V_OBF__aacc, V_OBF__aabb) & $true))).
