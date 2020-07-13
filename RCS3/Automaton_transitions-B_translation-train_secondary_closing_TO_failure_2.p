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

tff(power, type, power: ($int * $int) > $int).

tff(power_0, axiom, ![X:$int]: (power(X, 0) = 1)).

tff(power_s, axiom, ![X:$int, N:$int]: ($lesseq(0,N) => (power(X,
  $sum(N,1)) = $product(X,power(X, N))))).

tff(power_s_alt, axiom, ![X:$int, N:$int]: ($less(0,N) => (power(X,
  N) = $product(X,power(X, $difference(N,1)))))).

tff(power_1, axiom, ![X:$int]: (power(X, 1) = X)).

tff(power_sum, axiom, ![X:$int, N:$int, M:$int]: ($lesseq(0,N)
  => ($lesseq(0,M) => (power(X, $sum(N,M)) = $product(power(X, N),power(X,
  M)))))).

tff(power_mult, axiom, ![X:$int, N:$int, M:$int]: ($lesseq(0,N)
  => ($lesseq(0,M) => (power(X, $product(N,M)) = power(power(X, N), M))))).

tff(power_mult2, axiom, ![X:$int, Y:$int, N:$int]: ($lesseq(0,N)
  => (power($product(X,Y), N) = $product(power(X, N),power(Y, N))))).

tff(power_non_neg, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $lesseq(0,Y))
  => $lesseq(0,power(X, Y)))).

tff(power_monotonic, axiom, ![X:$int, N:$int, M:$int]: (($less(0,X)
  & ($lesseq(0,N) & $lesseq(N,M))) => $lesseq(power(X, N),power(X, M)))).

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

tff(power1, type, power1: !>[A : $tType]: (set(A) > set(set(A)))).

tff(non_empty_power, type, non_empty_power: !>[A : $tType]: (set(A) >
  set(set(A)))).

tff(subset, type, subset: !>[A : $tType]: ((set(A) * set(A)) > $o)).

tff(subset_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]: (subset(A, S, T)
  <=> mem(set(A), S, power1(A, T)))).

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
  power1(A, T)) <=> ![X:A]: (mem(A, X, S) => mem(A, X, T)))).

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

tff(enum_t_AUTOMATON_STATE, type, enum_t_AUTOMATON_STATE: $tType).

tff(e_empty_open, type, e_empty_open: enum_t_AUTOMATON_STATE).

tff(e_train_open, type, e_train_open: enum_t_AUTOMATON_STATE).

tff(e_train_primary_closing, type, e_train_primary_closing:
  enum_t_AUTOMATON_STATE).

tff(e_train_secondary_wait, type, e_train_secondary_wait:
  enum_t_AUTOMATON_STATE).

tff(e_train_secondary_closing, type, e_train_secondary_closing:
  enum_t_AUTOMATON_STATE).

tff(e_train_closed, type, e_train_closed: enum_t_AUTOMATON_STATE).

tff(e_empty_closed, type, e_empty_closed: enum_t_AUTOMATON_STATE).

tff(e_empty_opening, type, e_empty_opening: enum_t_AUTOMATON_STATE).

tff(e_failure, type, e_failure: enum_t_AUTOMATON_STATE).

tff(match_enum_t_AUTOMATON_STATE, type, match_enum_t_AUTOMATON_STATE:
  !>[A : $tType]: ((enum_t_AUTOMATON_STATE * A * A * A * A * A * A * A * A *
  A) > A)).

tff(match_enum_t_AUTOMATON_STATE_E_empty_open, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_empty_open, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7, Z8) = Z)).

tff(match_enum_t_AUTOMATON_STATE_E_train_open, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_train_open, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7, Z8) = Z1)).

tff(match_enum_t_AUTOMATON_STATE_E_train_primary_closing, axiom,
  ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_train_primary_closing, Z, Z1, Z2, Z3,
  Z4, Z5, Z6, Z7, Z8) = Z2)).

tff(match_enum_t_AUTOMATON_STATE_E_train_secondary_wait, axiom,
  ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_train_secondary_wait, Z, Z1, Z2, Z3, Z4,
  Z5, Z6, Z7, Z8) = Z3)).

tff(match_enum_t_AUTOMATON_STATE_E_train_secondary_closing, axiom,
  ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_train_secondary_closing, Z, Z1, Z2, Z3,
  Z4, Z5, Z6, Z7, Z8) = Z4)).

tff(match_enum_t_AUTOMATON_STATE_E_train_closed, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_train_closed, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7, Z8) = Z5)).

tff(match_enum_t_AUTOMATON_STATE_E_empty_closed, axiom, ![A : $tType]: ![Z:A,
  Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_empty_closed, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7, Z8) = Z6)).

tff(match_enum_t_AUTOMATON_STATE_E_empty_opening, axiom, ![A : $tType]: ![Z:
  A, Z1:A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_empty_opening, Z, Z1, Z2, Z3, Z4, Z5,
  Z6, Z7, Z8) = Z7)).

tff(match_enum_t_AUTOMATON_STATE_E_failure, axiom, ![A : $tType]: ![Z:A, Z1:
  A, Z2:A, Z3:A, Z4:A, Z5:A, Z6:A, Z7:A, Z8:A]:
  (match_enum_t_AUTOMATON_STATE(A, e_failure, Z, Z1, Z2, Z3, Z4, Z5, Z6, Z7,
  Z8) = Z8)).

tff(e_empty_open_E_train_open, axiom, ~ (e_empty_open = e_train_open)).

tff(e_empty_open_E_train_primary_closing, axiom, ~
  (e_empty_open = e_train_primary_closing)).

tff(e_empty_open_E_train_secondary_wait, axiom, ~
  (e_empty_open = e_train_secondary_wait)).

tff(e_empty_open_E_train_secondary_closing, axiom, ~
  (e_empty_open = e_train_secondary_closing)).

tff(e_empty_open_E_train_closed, axiom, ~ (e_empty_open = e_train_closed)).

tff(e_empty_open_E_empty_closed, axiom, ~ (e_empty_open = e_empty_closed)).

tff(e_empty_open_E_empty_opening, axiom, ~ (e_empty_open = e_empty_opening)).

tff(e_empty_open_E_failure, axiom, ~ (e_empty_open = e_failure)).

tff(e_train_open_E_train_primary_closing, axiom, ~
  (e_train_open = e_train_primary_closing)).

tff(e_train_open_E_train_secondary_wait, axiom, ~
  (e_train_open = e_train_secondary_wait)).

tff(e_train_open_E_train_secondary_closing, axiom, ~
  (e_train_open = e_train_secondary_closing)).

tff(e_train_open_E_train_closed, axiom, ~ (e_train_open = e_train_closed)).

tff(e_train_open_E_empty_closed, axiom, ~ (e_train_open = e_empty_closed)).

tff(e_train_open_E_empty_opening, axiom, ~ (e_train_open = e_empty_opening)).

tff(e_train_open_E_failure, axiom, ~ (e_train_open = e_failure)).

tff(e_train_primary_closing_E_train_secondary_wait, axiom, ~
  (e_train_primary_closing = e_train_secondary_wait)).

tff(e_train_primary_closing_E_train_secondary_closing, axiom, ~
  (e_train_primary_closing = e_train_secondary_closing)).

tff(e_train_primary_closing_E_train_closed, axiom, ~
  (e_train_primary_closing = e_train_closed)).

tff(e_train_primary_closing_E_empty_closed, axiom, ~
  (e_train_primary_closing = e_empty_closed)).

tff(e_train_primary_closing_E_empty_opening, axiom, ~
  (e_train_primary_closing = e_empty_opening)).

tff(e_train_primary_closing_E_failure, axiom, ~
  (e_train_primary_closing = e_failure)).

tff(e_train_secondary_wait_E_train_secondary_closing, axiom, ~
  (e_train_secondary_wait = e_train_secondary_closing)).

tff(e_train_secondary_wait_E_train_closed, axiom, ~
  (e_train_secondary_wait = e_train_closed)).

tff(e_train_secondary_wait_E_empty_closed, axiom, ~
  (e_train_secondary_wait = e_empty_closed)).

tff(e_train_secondary_wait_E_empty_opening, axiom, ~
  (e_train_secondary_wait = e_empty_opening)).

tff(e_train_secondary_wait_E_failure, axiom, ~
  (e_train_secondary_wait = e_failure)).

tff(e_train_secondary_closing_E_train_closed, axiom, ~
  (e_train_secondary_closing = e_train_closed)).

tff(e_train_secondary_closing_E_empty_closed, axiom, ~
  (e_train_secondary_closing = e_empty_closed)).

tff(e_train_secondary_closing_E_empty_opening, axiom, ~
  (e_train_secondary_closing = e_empty_opening)).

tff(e_train_secondary_closing_E_failure, axiom, ~
  (e_train_secondary_closing = e_failure)).

tff(e_train_closed_E_empty_closed, axiom, ~
  (e_train_closed = e_empty_closed)).

tff(e_train_closed_E_empty_opening, axiom, ~
  (e_train_closed = e_empty_opening)).

tff(e_train_closed_E_failure, axiom, ~ (e_train_closed = e_failure)).

tff(e_empty_closed_E_empty_opening, axiom, ~
  (e_empty_closed = e_empty_opening)).

tff(e_empty_closed_E_failure, axiom, ~ (e_empty_closed = e_failure)).

tff(e_empty_opening_E_failure, axiom, ~ (e_empty_opening = e_failure)).

tff(enum_t_AUTOMATON_STATE_inversion, axiom, ![U:enum_t_AUTOMATON_STATE]:
  (((((((((U = e_empty_open) | (U = e_train_open))
  | (U = e_train_primary_closing)) | (U = e_train_secondary_wait))
  | (U = e_train_secondary_closing)) | (U = e_train_closed))
  | (U = e_empty_closed)) | (U = e_empty_opening)) | (U = e_failure))).

tff(set_enum_t_AUTOMATON_STATE, type, set_enum_t_AUTOMATON_STATE:
  set(enum_t_AUTOMATON_STATE)).

tff(set_enum_t_AUTOMATON_STATE_axiom, axiom, ![X:enum_t_AUTOMATON_STATE]:
  mem(enum_t_AUTOMATON_STATE, X, set_enum_t_AUTOMATON_STATE)).

tff(enum_t_BOOM_MOVEMENT_ORDER, type, enum_t_BOOM_MOVEMENT_ORDER: $tType).

tff(e_go_up, type, e_go_up: enum_t_BOOM_MOVEMENT_ORDER).

tff(e_go_down, type, e_go_down: enum_t_BOOM_MOVEMENT_ORDER).

tff(match_enum_t_BOOM_MOVEMENT_ORDER, type, match_enum_t_BOOM_MOVEMENT_ORDER:
  !>[A : $tType]: ((enum_t_BOOM_MOVEMENT_ORDER * A * A) > A)).

tff(match_enum_t_BOOM_MOVEMENT_ORDER_E_go_up, axiom, ![A : $tType]: ![Z:A,
  Z1:A]: (match_enum_t_BOOM_MOVEMENT_ORDER(A, e_go_up, Z, Z1) = Z)).

tff(match_enum_t_BOOM_MOVEMENT_ORDER_E_go_down, axiom, ![A : $tType]: ![Z:A,
  Z1:A]: (match_enum_t_BOOM_MOVEMENT_ORDER(A, e_go_down, Z, Z1) = Z1)).

tff(e_go_up_E_go_down, axiom, ~ (e_go_up = e_go_down)).

tff(enum_t_BOOM_MOVEMENT_ORDER_inversion, axiom, ![U:
  enum_t_BOOM_MOVEMENT_ORDER]: ((U = e_go_up) | (U = e_go_down))).

tff(set_enum_t_BOOM_MOVEMENT_ORDER, type, set_enum_t_BOOM_MOVEMENT_ORDER:
  set(enum_t_BOOM_MOVEMENT_ORDER)).

tff(set_enum_t_BOOM_MOVEMENT_ORDER_axiom, axiom, ![X:
  enum_t_BOOM_MOVEMENT_ORDER]: mem(enum_t_BOOM_MOVEMENT_ORDER, X,
  set_enum_t_BOOM_MOVEMENT_ORDER)).

tff(enum_t_BOOM_TYPE, type, enum_t_BOOM_TYPE: $tType).

tff(e_primary_boom, type, e_primary_boom: enum_t_BOOM_TYPE).

tff(e_secondary_boom, type, e_secondary_boom: enum_t_BOOM_TYPE).

tff(match_enum_t_BOOM_TYPE, type, match_enum_t_BOOM_TYPE: !>[A : $tType]:
  ((enum_t_BOOM_TYPE * A * A) > A)).

tff(match_enum_t_BOOM_TYPE_E_primary_boom, axiom, ![A : $tType]: ![Z:A, Z1:
  A]: (match_enum_t_BOOM_TYPE(A, e_primary_boom, Z, Z1) = Z)).

tff(match_enum_t_BOOM_TYPE_E_secondary_boom, axiom, ![A : $tType]: ![Z:A, Z1:
  A]: (match_enum_t_BOOM_TYPE(A, e_secondary_boom, Z, Z1) = Z1)).

tff(e_primary_boom_E_secondary_boom, axiom, ~
  (e_primary_boom = e_secondary_boom)).

tff(enum_t_BOOM_TYPE_inversion, axiom, ![U:enum_t_BOOM_TYPE]:
  ((U = e_primary_boom) | (U = e_secondary_boom))).

tff(set_enum_t_BOOM_TYPE, type, set_enum_t_BOOM_TYPE: set(enum_t_BOOM_TYPE)).

tff(set_enum_t_BOOM_TYPE_axiom, axiom, ![X:enum_t_BOOM_TYPE]:
  mem(enum_t_BOOM_TYPE, X, set_enum_t_BOOM_TYPE)).

tff(enum_t_DETECTOR, type, enum_t_DETECTOR: $tType).

tff(e_adc_detector, type, e_adc_detector: enum_t_DETECTOR).

tff(e_bdc_detector, type, e_bdc_detector: enum_t_DETECTOR).

tff(match_enum_t_DETECTOR, type, match_enum_t_DETECTOR: !>[A : $tType]:
  ((enum_t_DETECTOR * A * A) > A)).

tff(match_enum_t_DETECTOR_E_adc_detector, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_enum_t_DETECTOR(A, e_adc_detector, Z, Z1) = Z)).

tff(match_enum_t_DETECTOR_E_bdc_detector, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_enum_t_DETECTOR(A, e_bdc_detector, Z, Z1) = Z1)).

tff(e_adc_detector_E_bdc_detector, axiom, ~
  (e_adc_detector = e_bdc_detector)).

tff(enum_t_DETECTOR_inversion, axiom, ![U:enum_t_DETECTOR]:
  ((U = e_adc_detector) | (U = e_bdc_detector))).

tff(set_enum_t_DETECTOR, type, set_enum_t_DETECTOR: set(enum_t_DETECTOR)).

tff(set_enum_t_DETECTOR_axiom, axiom, ![X:enum_t_DETECTOR]:
  mem(enum_t_DETECTOR, X, set_enum_t_DETECTOR)).

tff(enum_t_GATE, type, enum_t_GATE: $tType).

tff(e_inbound_lineside_gate, type, e_inbound_lineside_gate: enum_t_GATE).

tff(e_outbound_lineside_gate, type, e_outbound_lineside_gate: enum_t_GATE).

tff(match_enum_t_GATE, type, match_enum_t_GATE: !>[A : $tType]:
  ((enum_t_GATE * A * A) > A)).

tff(match_enum_t_GATE_E_inbound_lineside_gate, axiom, ![A : $tType]: ![Z:A,
  Z1:A]: (match_enum_t_GATE(A, e_inbound_lineside_gate, Z, Z1) = Z)).

tff(match_enum_t_GATE_E_outbound_lineside_gate, axiom, ![A : $tType]: ![Z:A,
  Z1:A]: (match_enum_t_GATE(A, e_outbound_lineside_gate, Z, Z1) = Z1)).

tff(e_inbound_lineside_gate_E_outbound_lineside_gate, axiom, ~
  (e_inbound_lineside_gate = e_outbound_lineside_gate)).

tff(enum_t_GATE_inversion, axiom, ![U:enum_t_GATE]:
  ((U = e_inbound_lineside_gate) | (U = e_outbound_lineside_gate))).

tff(set_enum_t_GATE, type, set_enum_t_GATE: set(enum_t_GATE)).

tff(set_enum_t_GATE_axiom, axiom, ![X:enum_t_GATE]: mem(enum_t_GATE, X,
  set_enum_t_GATE)).

tff(enum_t_LINE, type, enum_t_LINE: $tType).

tff(e_inbound_line, type, e_inbound_line: enum_t_LINE).

tff(e_outbound_line, type, e_outbound_line: enum_t_LINE).

tff(match_enum_t_LINE, type, match_enum_t_LINE: !>[A : $tType]:
  ((enum_t_LINE * A * A) > A)).

tff(match_enum_t_LINE_E_inbound_line, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_enum_t_LINE(A, e_inbound_line, Z, Z1) = Z)).

tff(match_enum_t_LINE_E_outbound_line, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_enum_t_LINE(A, e_outbound_line, Z, Z1) = Z1)).

tff(e_inbound_line_E_outbound_line, axiom, ~
  (e_inbound_line = e_outbound_line)).

tff(enum_t_LINE_inversion, axiom, ![U:enum_t_LINE]: ((U = e_inbound_line)
  | (U = e_outbound_line))).

tff(set_enum_t_LINE, type, set_enum_t_LINE: set(enum_t_LINE)).

tff(set_enum_t_LINE_axiom, axiom, ![X:enum_t_LINE]: mem(enum_t_LINE, X,
  set_enum_t_LINE)).

tff(f1, type, f1: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f1_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f1(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
  & mem($int, V_maximum_train_length, integer))
  & $lesseq(0,V_maximum_train_length))
  & $lesseq(V_maximum_train_length,2147483647)) & ~
  (V_maximum_train_length = 0)) & mem($int, V_minimum_train_length, integer))
  & $lesseq(0,V_minimum_train_length))
  & $lesseq(V_minimum_train_length,2147483647)) & ~
  (V_minimum_train_length = 0)) & (V_maximum_train_length = 400))
  & (V_minimum_train_length = 50)) & mem($int, V_maximum_train_speed,
  integer)) & $lesseq(0,V_maximum_train_speed))
  & $lesseq(V_maximum_train_speed,2147483647)) & ~
  (V_maximum_train_speed = 0)) & (V_maximum_train_speed = 28))
  & mem($int, V_number_of_booms, mk(1, 2)))
  & mem($int, V_adc_start_to_crossing_start, integer))
  & $lesseq(0,V_adc_start_to_crossing_start))
  & $lesseq(V_adc_start_to_crossing_start,2147483647)) & ~
  (V_adc_start_to_crossing_start = 0))
  & mem($int, V_adc_end_to_crossing_start, integer))
  & $lesseq(0,V_adc_end_to_crossing_start))
  & $lesseq(V_adc_end_to_crossing_start,2147483647)) & ~
  (V_adc_end_to_crossing_start = 0))
  & mem($int, V_bdc_start_to_crossing_start, integer))
  & $lesseq(0,V_bdc_start_to_crossing_start))
  & $lesseq(V_bdc_start_to_crossing_start,2147483647)) & ~
  (V_bdc_start_to_crossing_start = 0)) & mem($int, V_crossing_end_to_bdc_end,
  integer)) & $lesseq(0,V_crossing_end_to_bdc_end))
  & $lesseq(V_crossing_end_to_bdc_end,2147483647)) & ~
  (V_crossing_end_to_bdc_end = 0))
  & mem($int, V_crossing_start_to_crossing_end, integer))
  & $lesseq(0,V_crossing_start_to_crossing_end))
  & $lesseq(V_crossing_start_to_crossing_end,2147483647)) & ~
  (V_crossing_start_to_crossing_end = 0))
  & (V_adc_start_to_crossing_start = 1000))
  & (V_adc_end_to_crossing_start = 950))
  & (V_bdc_start_to_crossing_start = 25)) & (V_crossing_end_to_bdc_end = 15))
  & (V_crossing_start_to_crossing_end = 10))
  & $lesseq(V_minimum_train_length,$difference(V_adc_start_to_crossing_start,V_adc_end_to_crossing_start)))
  & $lesseq(V_minimum_train_length,$sum($sum(V_bdc_start_to_crossing_start,V_crossing_start_to_crossing_end),V_crossing_end_to_bdc_end)))
  & $lesseq(30,div(V_adc_start_to_crossing_start, V_maximum_train_speed)))
  & (V_cycle_duration = 100)) & mem($int, V_closing_boom_timer__initial_time,
  integer)) & $lesseq(0,V_closing_boom_timer__initial_time))
  & $lesseq(V_closing_boom_timer__initial_time,2147483647)) & ~
  (V_closing_boom_timer__initial_time = 0))
  & mem($int, V_secondary_wait_timer__initial_time, integer))
  & $lesseq(0,V_secondary_wait_timer__initial_time))
  & $lesseq(V_secondary_wait_timer__initial_time,2147483647)) & ~
  (V_secondary_wait_timer__initial_time = 0))
  & mem($int, V_opening_boom_timer__initial_time, integer))
  & $lesseq(0,V_opening_boom_timer__initial_time))
  & $lesseq(V_opening_boom_timer__initial_time,2147483647)) & ~
  (V_opening_boom_timer__initial_time = 0))
  & mem($int, V_first_train_in_warning_timer__initial_time, integer))
  & $lesseq(0,V_first_train_in_warning_timer__initial_time))
  & $lesseq(V_first_train_in_warning_timer__initial_time,2147483647)) & ~
  (V_first_train_in_warning_timer__initial_time = 0))
  & mem($int, V_last_train_in_warning_timer__initial_time, integer))
  & $lesseq(0,V_last_train_in_warning_timer__initial_time))
  & $lesseq(V_last_train_in_warning_timer__initial_time,2147483647)) & ~
  (V_last_train_in_warning_timer__initial_time = 0))
  & (V_closing_boom_timer__initial_time = 8000))
  & (V_secondary_wait_timer__initial_time = 2000))
  & (V_opening_boom_timer__initial_time = 8000))
  & (V_first_train_in_warning_timer__initial_time = 10000))
  & (V_last_train_in_warning_timer__initial_time = 5000))
  & mem(set(tuple2($int, $int)), V_bijection_trains, seq($int, V_TRAINS)))
  & mem(set(tuple2($int, $int)), inverse($int, $int, V_bijection_trains),
  infix_plmngt($int, $int, V_TRAINS, natural)))
  & mem(set(tuple2($int, $int)), V_bijection_trains, infix_plmngt($int,
  $int, diff($int, natural, singleton($int, 0)), V_TRAINS)))
  & infix_eqeq($int, ran($int, $int, V_bijection_trains), V_TRAINS))
  & mem($int, V_max_number_of_trains, integer))
  & $lesseq(0,V_max_number_of_trains))
  & $lesseq(V_max_number_of_trains,2147483647)) & ~
  (V_max_number_of_trains = 0))
  & (V_max_number_of_trains = size($int, V_bijection_trains)))
  & $lesseq($sum(div($sum($sum(V_adc_start_to_crossing_start,V_crossing_start_to_crossing_end),V_crossing_end_to_bdc_end),
  V_minimum_train_length),1),V_max_number_of_trains))
  & mem(set($int), V_TRAINS, finite_subsets($int, integer))) & ~
  infix_eqeq($int, V_TRAINS, empty($int))) & $true) & $true) & $true)
  & $true) & $true) & $true) & $true) & $true) & $true) & $true)
  & mem(set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)), V_allowed_transitions,
  relation(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, set_enum_t_AUTOMATON_STATE,
  set_enum_t_AUTOMATON_STATE)))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_empty_open)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_empty_open),
  singleton(enum_t_AUTOMATON_STATE, e_train_open)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_train_open)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_train_open),
  singleton(enum_t_AUTOMATON_STATE, e_train_primary_closing)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_train_primary_closing)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_train_primary_closing),
  singleton(enum_t_AUTOMATON_STATE, e_train_secondary_wait)),
  singleton(enum_t_AUTOMATON_STATE, e_train_closed)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_train_secondary_wait)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_train_secondary_wait),
  singleton(enum_t_AUTOMATON_STATE, e_train_secondary_closing)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_train_secondary_closing)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_train_secondary_closing),
  singleton(enum_t_AUTOMATON_STATE, e_train_closed)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_train_closed)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_train_closed),
  singleton(enum_t_AUTOMATON_STATE, e_empty_closed)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_empty_closed)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_empty_closed),
  singleton(enum_t_AUTOMATON_STATE, e_empty_opening)),
  singleton(enum_t_AUTOMATON_STATE, e_train_closed)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_empty_opening)),
  union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, union(enum_t_AUTOMATON_STATE, singleton(enum_t_AUTOMATON_STATE, e_empty_opening),
  singleton(enum_t_AUTOMATON_STATE, e_empty_open)),
  singleton(enum_t_AUTOMATON_STATE, e_train_open)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))))
  & infix_eqeq(enum_t_AUTOMATON_STATE, image(enum_t_AUTOMATON_STATE,
  enum_t_AUTOMATON_STATE, V_allowed_transitions,
  singleton(enum_t_AUTOMATON_STATE, e_failure)),
  singleton(enum_t_AUTOMATON_STATE, e_failure))) & $true) & $true))).

tff(f3, type, f3: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f3_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f3(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> mem(set($int), empty($int), power1($int, V_TRAINS)))).

tff(f4, type, f4: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f4_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f4(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_open = e_train_open)))).

tff(f7, type, f7: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f7_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f7(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_open = e_train_primary_closing)))).

tff(f9, type, f9: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f9_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f9(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_open = e_train_secondary_closing)))).

tff(f10, type, f10: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f10_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f10(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_open = e_train_secondary_wait)))).

tff(f12, type, f12: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f12_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f12(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_open = e_empty_closed)))).

tff(f14, type, f14: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f14_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f14(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_open = e_empty_opening)))).

tff(f18, type, f18: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f18_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f18(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((((((((((((((((((((((((((((((((((((((((((($true & $true) & $true)
  & $true) & $true) & $true) & $true) & $true) & $true) & $true)
  & mem(set($int), V_inbound_trains_in_warning, power1($int, V_TRAINS)))
  & mem(set($int), V_outbound_trains_in_warning, power1($int, V_TRAINS)))
  & $true) & $true) & $true)
  & mem($int, V_closing_boom_timer__remaining_time, integer))
  & $lesseq(0,V_closing_boom_timer__remaining_time))
  & $lesseq(V_closing_boom_timer__remaining_time,2147483647)) & $true)
  & mem($int, V_secondary_wait_timer__remaining_time, integer))
  & $lesseq(0,V_secondary_wait_timer__remaining_time))
  & $lesseq(V_secondary_wait_timer__remaining_time,2147483647)) & $true)
  & mem($int, V_opening_boom_timer__remaining_time, integer))
  & $lesseq(0,V_opening_boom_timer__remaining_time))
  & $lesseq(V_opening_boom_timer__remaining_time,2147483647)) & $true)
  & mem($int, V_first_train_in_warning_timer__remaining_time, integer))
  & $lesseq(0,V_first_train_in_warning_timer__remaining_time))
  & $lesseq(V_first_train_in_warning_timer__remaining_time,2147483647))
  & $true) & mem($int, V_last_train_in_warning_timer__remaining_time,
  integer)) & $lesseq(0,V_last_train_in_warning_timer__remaining_time))
  & $lesseq(V_last_train_in_warning_timer__remaining_time,2147483647)) & (~
  (V_status = e_train_open)
  => (V_first_train_in_warning_timer__active = false)))
  & ((V_status = e_train_open)
  => (V_first_train_in_warning_timer__active = true))) & ((~
  (V_status = e_train_primary_closing) & ~
  (V_status = e_train_secondary_closing))
  => (V_closing_boom_timer__active = false)))
  & (((V_status = e_train_primary_closing)
  | (V_status = e_train_secondary_closing))
  => (V_closing_boom_timer__active = true))) & (~
  (V_status = e_train_secondary_wait)
  => (V_secondary_wait_timer__active = false)))
  & ((V_status = e_train_secondary_wait)
  => (V_secondary_wait_timer__active = true))) & (~
  (V_status = e_empty_closed)
  => (V_last_train_in_warning_timer__active = false)))
  & ((V_status = e_empty_closed)
  => (V_last_train_in_warning_timer__active = true))) & (~
  (V_status = e_empty_opening) => (V_opening_boom_timer__active = false)))
  & ((V_status = e_empty_opening) => (V_opening_boom_timer__active = true)))
  & (((V_status = e_train_secondary_wait)
  | (V_status = e_train_secondary_closing)) => (V_number_of_booms = 2)))
  & ((V_status = e_train_secondary_wait)
  => (V_primary_boom_closed_detector = true)))
  & ((V_status = e_train_secondary_closing)
  => (V_primary_boom_closed_detector = true))))).

tff(f19, type, f19: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f19_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f19(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ((V_inbound_safety_mode = true)
  | (V_outbound_safety_mode = true))))).

tff(f20, type, f20: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f20_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f20(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_failure = e_train_open)))).

tff(f22, type, f22: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f22_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f22(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_failure = e_train_primary_closing)))).

tff(f24, type, f24: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f24_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f24(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_failure = e_train_secondary_closing)))).

tff(f25, type, f25: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f25_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f25(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_failure = e_train_secondary_wait)))).

tff(f27, type, f27: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f27_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f27(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_failure = e_empty_closed)))).

tff(f29, type, f29: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f29_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f29(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_failure = e_empty_opening)))).

tff(f35, type, f35: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f35_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f35(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((($true & (V_initialised = true)) & (V_status = e_empty_open)) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int)) | ~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))))
  & (V_first_train_in_warning_timer__active = false)))).

tff(f36, type, f36: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f36_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f36(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_open = e_train_primary_closing)) & ~
  (e_train_open = e_train_secondary_closing)))).

tff(f39, type, f39: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f39_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f39(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_open = e_train_primary_closing)))).

tff(f41, type, f41: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f41_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f41(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_open = e_train_secondary_closing)))).

tff(f42, type, f42: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f42_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f42(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_open = e_train_secondary_wait)))).

tff(f45, type, f45: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f45_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f45(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_open = e_train_secondary_wait)))).

tff(f47, type, f47: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f47_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f47(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_open = e_empty_closed)))).

tff(f50, type, f50: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f50_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f50(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_open = e_empty_closed)))).

tff(f52, type, f52: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f52_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f52(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_open = e_empty_opening)))).

tff(f55, type, f55: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f55_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f55(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_open = e_empty_opening)))).

tff(f57, type, f57: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f57_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f57(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((($true & (V_initialised = true)) & (V_status = e_train_open))
  & (V_first_train_in_warning_timer__active = true))
  & (V_first_train_in_warning_timer__remaining_time = 0))
  & (V_closing_boom_timer__active = false)))).

tff(f58, type, f58: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f58_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f58(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_primary_closing = e_train_open)))).

tff(f59, type, f59: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f59_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f59(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_primary_closing = e_train_secondary_wait)))).

tff(f60, type, f60: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f60_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f60(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_primary_closing = e_train_secondary_wait)))).

tff(f61, type, f61: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f61_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f61(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_primary_closing = e_empty_closed)))).

tff(f62, type, f62: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f62_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f62(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_primary_closing = e_empty_closed)))).

tff(f63, type, f63: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f63_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f63(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_primary_closing = e_empty_opening)))).

tff(f64, type, f64: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f64_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f64(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_primary_closing = e_empty_opening)))).

tff(f65, type, f65: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f65_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f65(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_primary_closing = e_train_secondary_closing)))).

tff(f66, type, f66: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f66_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f66(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((($true & (V_initialised = true))
  & (V_status = e_train_primary_closing))
  & (V_closing_boom_timer__active = true))
  & (V_closing_boom_timer__remaining_time = 0)))).

tff(f67, type, f67: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f67_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f67(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_failure = e_train_open)))).

tff(f71, type, f71: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f71_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f71(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_failure = e_train_secondary_wait)))).

tff(f72, type, f72: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f72_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f72(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_failure = e_empty_closed)))).

tff(f73, type, f73: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f73_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f73(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_failure = e_empty_opening)))).

tff(f74, type, f74: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f74_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f74(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((($true & (V_initialised = true))
  & (V_status = e_train_primary_closing))
  & (V_closing_boom_timer__active = true))
  & $lesseq(1,V_closing_boom_timer__remaining_time))
  & (V_primary_boom_closed_detector = true)) & (V_number_of_booms = 1)))).

tff(f75, type, f75: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f75_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f75(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_closed = e_train_open)))).

tff(f76, type, f76: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f76_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f76(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_closed = e_train_open)))).

tff(f77, type, f77: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f77_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f77(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_closed = e_train_primary_closing)))).

tff(f78, type, f78: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f78_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f78(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_closed = e_train_secondary_closing)))).

tff(f79, type, f79: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f79_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f79(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_closed = e_train_secondary_wait)))).

tff(f80, type, f80: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f80_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f80(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_closed = e_train_secondary_wait)))).

tff(f81, type, f81: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f81_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f81(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_closed = e_empty_closed)))).

tff(f82, type, f82: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f82_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f82(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_closed = e_empty_closed)))).

tff(f83, type, f83: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f83_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f83(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_closed = e_empty_opening)))).

tff(f84, type, f84: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f84_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f84(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_closed = e_empty_opening)))).

tff(f85, type, f85: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f85_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f85(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((($true & (V_initialised = true))
  & (V_status = e_train_primary_closing))
  & (V_closing_boom_timer__active = true))
  & $lesseq(1,V_closing_boom_timer__remaining_time))
  & (V_primary_boom_closed_detector = true)) & (V_number_of_booms = 2)))).

tff(f86, type, f86: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f86_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f86(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_secondary_wait = e_train_open)))).

tff(f87, type, f87: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f87_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f87(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_wait = e_train_open)))).

tff(f88, type, f88: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f88_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f88(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_wait = e_train_primary_closing)))).

tff(f89, type, f89: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f89_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f89(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_wait = e_train_secondary_closing)))).

tff(f90, type, f90: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f90_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f90(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_secondary_wait = e_empty_closed)))).

tff(f91, type, f91: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f91_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f91(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_wait = e_empty_closed)))).

tff(f92, type, f92: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f92_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f92(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_secondary_wait = e_empty_opening)))).

tff(f93, type, f93: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f93_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f93(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_wait = e_empty_opening)))).

tff(f94, type, f94: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f94_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f94(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((($true & (V_initialised = true))
  & (V_status = e_train_secondary_wait))
  & (V_secondary_wait_timer__active = true))
  & (V_secondary_wait_timer__remaining_time = 0)))).

tff(f95, type, f95: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f95_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f95(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_secondary_closing = e_train_open)))).

tff(f96, type, f96: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f96_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f96(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_closing = e_train_open)))).

tff(f97, type, f97: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f97_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f97(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_closing = e_train_secondary_wait)))).

tff(f98, type, f98: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f98_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f98(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_secondary_closing = e_empty_closed)))).

tff(f99, type, f99: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f99_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f99(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_closing = e_empty_closed)))).

tff(f100, type, f100: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f100_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f100(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_secondary_closing = e_empty_opening)))).

tff(f101, type, f101: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f101_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f101(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true)))
  & (e_train_secondary_closing = e_empty_opening)))).

tff(f102, type, f102: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f102_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f102(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))))).

tff(f103, type, f103: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f103_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f103(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((($true & (V_initialised = true))
  & (V_status = e_train_secondary_closing))
  & (V_closing_boom_timer__active = true))
  & (V_closing_boom_timer__remaining_time = 0)))).

tff(f104, type, f104: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f104_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f104(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((($true & (V_initialised = true))
  & (V_status = e_train_secondary_closing))
  & (V_closing_boom_timer__active = true))
  & $lesseq(1,V_closing_boom_timer__remaining_time))
  & (V_secondary_boom_closed_detector = true)))).

tff(f105, type, f105: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f105_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f105(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((($true & (V_initialised = true)) & (V_status = e_train_closed))
  & infix_eqeq($int, V_inbound_trains_in_warning, empty($int)))
  & infix_eqeq($int, V_outbound_trains_in_warning, empty($int)))
  & (V_last_train_in_warning_timer__active = false)))).

tff(f106, type, f106: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f106_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f106(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_closed = e_train_open)))).

tff(f107, type, f107: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f107_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f107(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_closed = e_train_open)))).

tff(f108, type, f108: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f108_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f108(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (($true & ~ (e_empty_closed = e_train_primary_closing)) & ~
  (e_empty_closed = e_train_secondary_closing)))).

tff(f109, type, f109: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f109_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f109(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_closed = e_train_primary_closing)))).

tff(f110, type, f110: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f110_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f110(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_closed = e_train_secondary_closing)))).

tff(f111, type, f111: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f111_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f111(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_closed = e_train_secondary_wait)))).

tff(f112, type, f112: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f112_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f112(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_closed = e_train_secondary_wait)))).

tff(f113, type, f113: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f113_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f113(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_closed = e_empty_opening)))).

tff(f114, type, f114: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f114_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f114(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_closed = e_empty_opening)))).

tff(f115, type, f115: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f115_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f115(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((($true & (V_initialised = true)) & (V_status = e_empty_closed)) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int)) | ~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))))
  & (V_last_train_in_warning_timer__active = true)))).

tff(f116, type, f116: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f116_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f116(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((((($true & $true) & $true)
  & (infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_inbound_trains_in_warning, empty($int))
  => (V_inbound_indicators_on_1 = true)))
  & (infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = false))) & (~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))
  => (V_outbound_indicators_on_1 = true))) & ~
  (e_train_closed = e_train_primary_closing)) & ~
  (e_train_closed = e_train_secondary_closing)))).

tff(f117, type, f117: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f117_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f117(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((((((($true & (V_initialised = true)) & (V_status = e_empty_closed))
  & infix_eqeq($int, V_inbound_trains_in_warning, empty($int)))
  & infix_eqeq($int, V_outbound_trains_in_warning, empty($int)))
  & (V_last_train_in_warning_timer__active = true))
  & (V_last_train_in_warning_timer__remaining_time = 0))
  & (V_opening_boom_timer__active = false))
  & (V_boom_safety_close = false)))).

tff(f118, type, f118: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f118_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f118(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_opening = e_train_open)))).

tff(f119, type, f119: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f119_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f119(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_opening = e_train_open)))).

tff(f120, type, f120: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f120_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f120(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (($true & ~ (e_empty_opening = e_train_primary_closing)) & ~
  (e_empty_opening = e_train_secondary_closing)))).

tff(f121, type, f121: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f121_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f121(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_opening = e_train_primary_closing)))).

tff(f122, type, f122: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f122_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f122(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_opening = e_train_secondary_closing)))).

tff(f123, type, f123: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f123_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f123(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_opening = e_train_secondary_wait)))).

tff(f124, type, f124: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f124_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f124(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_opening = e_train_secondary_wait)))).

tff(f125, type, f125: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f125_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f125(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & (e_empty_opening = e_empty_closed)))).

tff(f126, type, f126: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f126_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f126(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (((($true & (V_initialised = true)) & (V_status = e_empty_opening))
  & (V_opening_boom_timer__active = true))
  & (V_opening_boom_timer__remaining_time = 0)))).

tff(f127, type, f127: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f127_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f127(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (($true & ~ (e_failure = e_train_primary_closing)) & ~
  (e_failure = e_train_secondary_closing)))).

tff(f128, type, f128: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f128_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f128(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((((($true & (V_initialised = true)) & (V_status = e_empty_opening))
  & infix_eqeq($int, V_inbound_trains_in_warning, empty($int)))
  & infix_eqeq($int, V_outbound_trains_in_warning, empty($int)))
  & (V_opening_boom_timer__active = true))
  & $lesseq(1,V_opening_boom_timer__remaining_time))
  & (V_boom_open_detector = true)))).

tff(f129, type, f129: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f129_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f129(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_open = e_train_open)))).

tff(f130, type, f130: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f130_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f130(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> (($true & ~ (e_empty_open = e_train_primary_closing)) & ~
  (e_empty_open = e_train_secondary_closing)))).

tff(f131, type, f131: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f131_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f131(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_open = e_train_secondary_wait)))).

tff(f132, type, f132: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f132_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f132(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ($true & ~ (e_empty_open = e_empty_closed)))).

tff(f133, type, f133: (enum_t_AUTOMATON_STATE * $int * $int * bool * bool *
  bool * set($int) * bool * bool * bool * $int * $int * bool * $int * $int *
  $int * $int * $int * $int * $int * bool * bool * bool * set($int) * bool *
  bool * bool * $int * $int * bool * $int * $int * $int * $int * $int *
  bool * bool * bool * set(tuple2($int, $int)) * $int *
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)) * $int * $int *
  set($int)) > $o).

tff(f133_def, axiom, ![V_status:enum_t_AUTOMATON_STATE,
  V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: (f133(V_status,
  V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  <=> ((((($true & (V_initialised = true)) & (V_status = e_empty_opening))
  & (~ infix_eqeq($int, V_inbound_trains_in_warning, empty($int)) | ~
  infix_eqeq($int, V_outbound_trains_in_warning, empty($int))))
  & (V_opening_boom_timer__active = true))
  & (V_first_train_in_warning_timer__active = false)))).

tff(train_secondary_closing_TO_failure_2, conjecture, ![V_status:
  enum_t_AUTOMATON_STATE, V_secondary_wait_timer__remaining_time:$int,
  V_secondary_wait_timer__initial_time:$int, V_secondary_wait_timer__active:
  bool, V_secondary_boom_closed_detector:bool,
  V_primary_boom_closed_detector:bool, V_outbound_trains_in_warning:
  set($int), V_outbound_safety_mode:bool, V_outbound_indicators_on_1:bool,
  V_outbound_indicators_on:bool, V_opening_boom_timer__remaining_time:$int,
  V_opening_boom_timer__initial_time:$int, V_opening_boom_timer__active:bool,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_last_train_in_warning_timer__remaining_time:$int,
  V_last_train_in_warning_timer__initial_time:$int,
  V_last_train_in_warning_timer__active:bool, V_lamps_bells_on:bool,
  V_initialised:bool, V_inbound_trains_in_warning:set($int),
  V_inbound_safety_mode:bool, V_inbound_indicators_on_1:bool,
  V_inbound_indicators_on:bool,
  V_first_train_in_warning_timer__remaining_time:$int,
  V_first_train_in_warning_timer__initial_time:$int,
  V_first_train_in_warning_timer__active:bool, V_cycle_duration:$int,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__remaining_time:$int,
  V_closing_boom_timer__initial_time:$int, V_closing_boom_timer__active:bool,
  V_boom_safety_close:bool, V_boom_open_detector:bool, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_start_to_crossing_start:$int,
  V_allowed_transitions:
  set(tuple2(enum_t_AUTOMATON_STATE, enum_t_AUTOMATON_STATE)),
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int)]: ((f1(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  & (f18(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  & (f20(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  & ($true & (f103(V_status, V_secondary_wait_timer__remaining_time,
  V_secondary_wait_timer__initial_time, V_secondary_wait_timer__active,
  V_secondary_boom_closed_detector, V_primary_boom_closed_detector,
  V_outbound_trains_in_warning, V_outbound_safety_mode,
  V_outbound_indicators_on_1, V_outbound_indicators_on,
  V_opening_boom_timer__remaining_time, V_opening_boom_timer__initial_time,
  V_opening_boom_timer__active, V_number_of_booms, V_minimum_train_length,
  V_maximum_train_speed, V_maximum_train_length, V_max_number_of_trains,
  V_last_train_in_warning_timer__remaining_time,
  V_last_train_in_warning_timer__initial_time,
  V_last_train_in_warning_timer__active, V_lamps_bells_on, V_initialised,
  V_inbound_trains_in_warning, V_inbound_safety_mode,
  V_inbound_indicators_on_1, V_inbound_indicators_on,
  V_first_train_in_warning_timer__remaining_time,
  V_first_train_in_warning_timer__initial_time,
  V_first_train_in_warning_timer__active, V_cycle_duration,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__remaining_time, V_closing_boom_timer__initial_time,
  V_closing_boom_timer__active, V_boom_safety_close, V_boom_open_detector,
  V_bijection_trains, V_bdc_start_to_crossing_start, V_allowed_transitions,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS)
  & $true))))) => ((V_first_train_in_warning_timer__active = true)
  & $true))).
