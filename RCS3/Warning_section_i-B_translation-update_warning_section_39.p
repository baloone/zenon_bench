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

tff(f1, type, f1: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f1_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f1(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((($true
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
  & $true) & $true) & $true) & $true) & $true) & $true) & $true))).

tff(f2, type, f2: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f2_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f2(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((((($true & $true) & $true) & $true) & $true) & $true) & $true)
  & $true) & $true) & $true) & $true) & $true) & $true))).

tff(f3, type, f3: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f3_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f3(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (($true & $true) & $true))).

tff(f4, type, f4: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f4_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f4(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & $true))).

tff(f5, type, f5: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f5_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f5(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1, 0)),
  empty($int)))).

tff(f7, type, f7: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f7_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f7(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> mem($int, 0, mk(0, V_max_number_of_trains)))).

tff(f9, type, f9: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f9_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f9(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((((((((((((((((((($true & $true) & $true) & $true) & $true)
  & mem(set($int), V_trains_in_warning, power1($int, V_TRAINS))) & $true)
  & $true)
  & $lesseq(V_maximum_train_length,$difference(V_adc_end_to_crossing_start,V_bdc_start_to_crossing_start)))
  & $true) & mem($int, V_train_counter_1, mk(0, V_max_number_of_trains)))
  & infix_eqeq($int, V_trains_in_warning, image($int,
  $int, V_bijection_trains, mk(1, V_train_counter_1))))
  & (infix_eqeq($int, V_trains_in_warning, empty($int))
  => (V_train_counter_1 = 0))) & ((V_train_counter_1 = 0)
  => infix_eqeq($int, V_trains_in_warning, empty($int))))
  & ((V_initialised = true) => ((V_ADCinitialised_1 = true)
  & (V_BDCinitialised_1 = true)))) & ((V_initialised = false)
  => ((V_ADCinitialised_1 = false) & (V_BDCinitialised_1 = false))))
  & ((V_initialised = true) => ((V_ADCadc_or_bdc_kind_1 = e_adc_detector)
  & (V_BDCadc_or_bdc_kind_1 = e_bdc_detector)))) & ((V_initialised = true)
  => (V_ADCline_kind_1 = V_BDCline_kind_1)))
  & (V_ADCupdated_detector_1 = false)) & (V_BDCupdated_detector_1 = false))
  & (V_line_kind = V_line_kind_1)) & (V_adc_state = V_adc_state_1))
  & (V_bdc_state = V_bdc_state_1)) & (V_safety_mode = V_safety_mode_1)))).

tff(f10, type, f10: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f10_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f10(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (($true & $true) & (V_initialised = false)))).

tff(f11, type, f11: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f11_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f11(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (($true & $true) & (V_initialised = false)))).

tff(f15, type, f15: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f15_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f15(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & (V_initialised = true)))).

tff(f16, type, f16: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f16_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f16(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & (V_initialised = true)))).

tff(f18, type, f18: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f18_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f18(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((($true & (V_initialised = true)) & $true) & $true))).

tff(f20, type, f20: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f20_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f20(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((($true & (V_initialised = true)) & $true) & $true) & $true))).

tff(f21, type, f21: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f21_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f21(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((($true & (V_initialised = true)) & $true) & $true) & $true)
  & $true) & ((((V_ADCadc_or_bdc_kind_1 = e_adc_detector)
  & (V_ADCcurrent_track_circuit_1 = false))
  & (V_current_track_circuit_0 = true)) => (V_ret_1 = true)))
  & ((((V_ADCadc_or_bdc_kind_1 = e_bdc_detector)
  & (V_ADCcurrent_track_circuit_1 = true))
  & (V_current_track_circuit_0 = false)) => (V_ret_1 = true))) & ((~
  (((V_ADCadc_or_bdc_kind_1 = e_adc_detector)
  & (V_ADCcurrent_track_circuit_1 = false))
  & (V_current_track_circuit_0 = true)) & ~
  (((V_ADCadc_or_bdc_kind_1 = e_bdc_detector)
  & (V_ADCcurrent_track_circuit_1 = true))
  & (V_current_track_circuit_0 = false))) => (V_ret_1 = false))))).

tff(f22, type, f22: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f22_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f22(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & (V_initialised = true)))).

tff(f23, type, f23: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f23_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f23(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((($true & (V_initialised = true)) & $true)
  & (V_bdc_state_1 = false)) & (V_adc_state_1 = true))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains)))).

tff(f24, type, f24: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f24_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f24(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> mem($int, $sum(V_train_counter_1,1), integer))).

tff(f25, type, f25: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f25_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f25(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> $lesseq($sum(V_train_counter_1,1),2147483647))).

tff(f26, type, f26: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f26_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f26(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> $lesseq($uminus(2147483647),$sum(V_train_counter_1,1)))).

tff(f30, type, f30: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f30_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f30(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false)))
  & (V_bdc_state_1 = true)) & (V_adc_state_1 = false))
  & $lesseq(1,V_train_counter_1)))).

tff(f31, type, f31: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f31_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f31(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> mem($int, $difference(V_train_counter_1,1), integer))).

tff(f32, type, f32: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f32_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f32(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> $lesseq($difference(V_train_counter_1,1),2147483647))).

tff(f33, type, f33: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f33_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f33(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> $lesseq($uminus(2147483647),$difference(V_train_counter_1,1)))).

tff(f34, type, f34: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f34_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f34(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true)
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false)) & ~
  infix_eqeq($int, V_trains_in_warning, V_TRAINS)))).

tff(f36, type, f36: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f36_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f36(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ?[V_train:$int]: ((mem($int, V_train, V_TRAINS) & ~ mem($int, V_train,
  V_trains_in_warning)) & infix_eqeq($int, image($int,
  $int, V_bijection_trains, mk(1, $sum(V_train_counter_1,1))),
  union($int, V_trains_in_warning, singleton($int, V_train)))))).

tff(f37, type, f37: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f37_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f37(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true)
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false))
  & infix_eqeq($int, V_trains_in_warning, V_TRAINS)))).

tff(f38, type, f38: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f38_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f38(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  $sum(V_train_counter_1,1))), V_trains_in_warning))).

tff(f41, type, f41: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f41_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f41(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((($true & (V_initialised = true)) & $true)
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false)))).

tff(f43, type, f43: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f43_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f43(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> mem($int, $sum(V_train_counter_1,1), mk(0, V_max_number_of_trains)))).

tff(f44, type, f44: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f44_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f44(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true)
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false))
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  $sum(V_train_counter_1,1))), empty($int))))).

tff(f46, type, f46: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f46_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f46(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($sum(V_train_counter_1,1) = 0))).

tff(f47, type, f47: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f47_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f47(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true)
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false))
  & ($sum(V_train_counter_1,1) = 0)))).

tff(f48, type, f48: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f48_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f48(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  $sum(V_train_counter_1,1))), empty($int)))).

tff(f49, type, f49: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f49_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f49(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true) & ~
  $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false)) & ~
  infix_eqeq($int, V_trains_in_warning, V_TRAINS)))).

tff(f50, type, f50: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f50_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f50(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ?[V_train:$int]: ((mem($int, V_train, V_TRAINS) & ~ mem($int, V_train,
  V_trains_in_warning)) & infix_eqeq($int, image($int,
  $int, V_bijection_trains, mk(1, V_train_counter_1)),
  union($int, V_trains_in_warning, singleton($int, V_train)))))).

tff(f51, type, f51: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f51_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f51(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true) & ~
  $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false))
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  V_train_counter_1)), empty($int))))).

tff(f53, type, f53: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f53_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f53(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true) & ~
  $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = false))
  & (V_train_counter_1 = 0)))).

tff(f54, type, f54: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f54_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f54(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  V_train_counter_1)), empty($int)))).

tff(f55, type, f55: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f55_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f55(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false)))
  & $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & ~ infix_eqeq($int, V_trains_in_warning,
  empty($int))))).

tff(f56, type, f56: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f56_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f56(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ?[V_train:$int]: (mem($int, V_train, V_trains_in_warning)
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  $difference(V_train_counter_1,1))), diff($int, V_trains_in_warning,
  singleton($int, V_train)))))).

tff(f57, type, f57: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f57_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f57(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false)))
  & $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & infix_eqeq($int, V_trains_in_warning,
  empty($int))))).

tff(f58, type, f58: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f58_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f58(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  $difference(V_train_counter_1,1))), V_trains_in_warning))).

tff(f59, type, f59: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f59_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f59(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false)))
  & $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)))).

tff(f60, type, f60: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f60_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f60(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> mem($int, $difference(V_train_counter_1,1), mk(0,
  V_max_number_of_trains)))).

tff(f61, type, f61: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f61_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f61(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false)))
  & $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & infix_eqeq($int, image($int,
  $int, V_bijection_trains, mk(1, $difference(V_train_counter_1,1))),
  empty($int))))).

tff(f62, type, f62: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f62_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f62(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($difference(V_train_counter_1,1) = 0))).

tff(f63, type, f63: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f63_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f63(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false)))
  & $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & ($difference(V_train_counter_1,1) = 0)))).

tff(f64, type, f64: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f64_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f64(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  $difference(V_train_counter_1,1))), empty($int)))).

tff(f65, type, f65: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f65_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f65(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & ~ infix_eqeq($int, V_trains_in_warning,
  empty($int))))).

tff(f66, type, f66: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f66_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f66(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ?[V_train:$int]: (mem($int, V_train, V_trains_in_warning)
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  V_train_counter_1)), diff($int, V_trains_in_warning,
  singleton($int, V_train)))))).

tff(f67, type, f67: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f67_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f67(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & infix_eqeq($int, image($int,
  $int, V_bijection_trains, mk(1, V_train_counter_1)), empty($int))))).

tff(f68, type, f68: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f68_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f68(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  $lesseq(1,V_train_counter_1)) & (V_adc_state_1 = false))
  & (V_bdc_state_1 = true)) & (V_train_counter_1 = 0)))).

tff(f69, type, f69: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f69_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f69(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & (V_adc_state_1 = false)) & (V_bdc_state_1 = false))
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  V_train_counter_1)), empty($int))))).

tff(f70, type, f70: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f70_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f70(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & (V_adc_state_1 = false)) & (V_bdc_state_1 = false))
  & (V_train_counter_1 = 0)))).

tff(f71, type, f71: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f71_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f71(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true))
  & (V_bdc_state_1 = false)) & ~ infix_eqeq($int, V_trains_in_warning,
  V_TRAINS)))).

tff(f72, type, f72: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f72_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f72(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true))
  & (V_bdc_state_1 = false)) & infix_eqeq($int, V_trains_in_warning,
  V_TRAINS)))).

tff(f73, type, f73: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f73_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f73(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true))
  & (V_adc_state_1 = false)) & ~ infix_eqeq($int, V_trains_in_warning,
  empty($int))))).

tff(f74, type, f74: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f74_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f74(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true))
  & (V_adc_state_1 = false)) & infix_eqeq($int, V_trains_in_warning,
  empty($int))))).

tff(f75, type, f75: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f75_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f75(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true)) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true)) & ~
  infix_eqeq($int, V_trains_in_warning, empty($int))) & ~
  infix_eqeq($int, V_trains_in_warning, V_TRAINS))))).

tff(f76, type, f76: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f76_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f76(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true))
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  V_train_counter_1)), empty($int))))).

tff(f77, type, f77: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f77_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f77(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true)))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))
  & (V_adc_state_1 = true)) & (V_bdc_state_1 = true))
  & (V_train_counter_1 = 0)))).

tff(f78, type, f78: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f78_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f78(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains)))
  & (V_bdc_state_1 = false)) & (V_adc_state_1 = true)) & ~
  infix_eqeq($int, V_trains_in_warning, V_TRAINS)))).

tff(f79, type, f79: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f79_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f79(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains)))
  & (V_bdc_state_1 = true)) & (V_adc_state_1 = false)) & ~
  infix_eqeq($int, V_trains_in_warning, empty($int))))).

tff(f80, type, f80: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f80_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f80(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains)))
  & (V_bdc_state_1 = false)) & (V_adc_state_1 = false)))).

tff(f81, type, f81: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f81_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f81(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> (((((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains))) & ~
  infix_eqeq($int, V_trains_in_warning, empty($int))) & ~
  infix_eqeq($int, V_trains_in_warning, V_TRAINS)) & (V_adc_state_1 = true))
  & (V_bdc_state_1 = true)))).

tff(f82, type, f82: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f82_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f82(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains)))
  & infix_eqeq($int, image($int, $int, V_bijection_trains, mk(1,
  V_train_counter_1)), empty($int))))).

tff(f83, type, f83: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f83_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f83(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((((((($true & (V_initialised = true)) & $true) & ~
  ((V_adc_state_1 = true) & (V_bdc_state_1 = false))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = true))) & ~
  ((V_adc_state_1 = false) & (V_bdc_state_1 = false))) & ~
  ((((V_adc_state_1 = true) & (V_bdc_state_1 = true))
  & $lesseq(1,V_train_counter_1))
  & $lesseq($sum(V_train_counter_1,1),V_max_number_of_trains)))
  & (V_train_counter_1 = 0)))).

tff(f84, type, f84: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f84_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f84(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & (V_initialised = true)))).

tff(f85, type, f85: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f85_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f85(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & (V_initialised = true)))).

tff(f86, type, f86: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f86_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f86(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ($true & $true))).

tff(f87, type, f87: (set($int) * $int * $int * $int * bool * bool * bool *
  $int * $int * $int * $int * $int * $int * enum_t_LINE * enum_t_LINE *
  enum_t_LINE * $int * bool * $int * $int * bool * bool * $int * $int *
  $int * set(tuple2($int, $int)) * bool * bool * $int * bool * bool * $int *
  $int * set($int) * bool * bool * bool * bool * enum_t_LINE * enum_t_LINE *
  bool * bool * bool * bool * enum_t_DETECTOR * enum_t_DETECTOR * bool *
  bool * bool * bool * enum_t_LINE * enum_t_LINE * bool * bool * bool *
  bool * enum_t_DETECTOR * enum_t_DETECTOR) > $o).

tff(f87_def, axiom, ![V_trains_in_warning:set($int), V_train_counter_1:$int,
  V_train_counter:$int, V_secondary_wait_timer__initial_time:$int,
  V_safety_mode_1:bool, V_safety_mode:bool, V_ret_1:bool,
  V_opening_boom_timer__initial_time:$int, V_number_of_booms:$int,
  V_minimum_train_length:$int, V_maximum_train_speed:$int,
  V_maximum_train_length:$int, V_max_number_of_trains:$int, V_line_kind_1:
  enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: (f87(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  <=> ((V_train_counter_1 = 0) <=> infix_eqeq($int, V_trains_in_warning,
  empty($int))))).

tff(update_warning_section_39, conjecture, ![V_trains_in_warning:set($int),
  V_train_counter_1:$int, V_train_counter:$int,
  V_secondary_wait_timer__initial_time:$int, V_safety_mode_1:bool,
  V_safety_mode:bool, V_ret_1:bool, V_opening_boom_timer__initial_time:$int,
  V_number_of_booms:$int, V_minimum_train_length:$int, V_maximum_train_speed:
  $int, V_maximum_train_length:$int, V_max_number_of_trains:$int,
  V_line_kind_1:enum_t_LINE, V_line_kind:enum_t_LINE, V_line:enum_t_LINE,
  V_last_train_in_warning_timer__initial_time:$int, V_initialised:bool,
  V_first_train_in_warning_timer__initial_time:$int, V_cycle_duration:$int,
  V_current_track_circuit_1:bool, V_current_track_circuit_0:bool,
  V_crossing_start_to_crossing_end:$int, V_crossing_end_to_bdc_end:$int,
  V_closing_boom_timer__initial_time:$int, V_bijection_trains:
  set(tuple2($int, $int)), V_bdc_state_1:bool, V_bdc_state:bool,
  V_bdc_start_to_crossing_start:$int, V_adc_state_1:bool, V_adc_state:bool,
  V_adc_start_to_crossing_start:$int, V_adc_end_to_crossing_start:$int,
  V_TRAINS:set($int), V_BDCupdated_detector_1:bool, V_BDCupdated_detector:
  bool, V_BDCprevious_track_circuit_1:bool, V_BDCprevious_track_circuit:bool,
  V_BDCline_kind_1:enum_t_LINE, V_BDCline_kind:enum_t_LINE,
  V_BDCinitialised_1:bool, V_BDCinitialised:bool,
  V_BDCcurrent_track_circuit_1:bool, V_BDCcurrent_track_circuit:bool,
  V_BDCadc_or_bdc_kind_1:enum_t_DETECTOR, V_BDCadc_or_bdc_kind:
  enum_t_DETECTOR, V_ADCupdated_detector_1:bool, V_ADCupdated_detector:bool,
  V_ADCprevious_track_circuit_1:bool, V_ADCprevious_track_circuit:bool,
  V_ADCline_kind_1:enum_t_LINE, V_ADCline_kind:enum_t_LINE,
  V_ADCinitialised_1:bool, V_ADCinitialised:bool,
  V_ADCcurrent_track_circuit_1:bool, V_ADCcurrent_track_circuit:bool,
  V_ADCadc_or_bdc_kind_1:enum_t_DETECTOR, V_ADCadc_or_bdc_kind:
  enum_t_DETECTOR]: ((f1(V_trains_in_warning, V_train_counter_1,
  V_train_counter, V_secondary_wait_timer__initial_time, V_safety_mode_1,
  V_safety_mode, V_ret_1, V_opening_boom_timer__initial_time,
  V_number_of_booms, V_minimum_train_length, V_maximum_train_speed,
  V_maximum_train_length, V_max_number_of_trains, V_line_kind_1, V_line_kind,
  V_line, V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  & (f2(V_trains_in_warning, V_train_counter_1, V_train_counter,
  V_secondary_wait_timer__initial_time, V_safety_mode_1, V_safety_mode,
  V_ret_1, V_opening_boom_timer__initial_time, V_number_of_booms,
  V_minimum_train_length, V_maximum_train_speed, V_maximum_train_length,
  V_max_number_of_trains, V_line_kind_1, V_line_kind, V_line,
  V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  & (f9(V_trains_in_warning, V_train_counter_1, V_train_counter,
  V_secondary_wait_timer__initial_time, V_safety_mode_1, V_safety_mode,
  V_ret_1, V_opening_boom_timer__initial_time, V_number_of_booms,
  V_minimum_train_length, V_maximum_train_speed, V_maximum_train_length,
  V_max_number_of_trains, V_line_kind_1, V_line_kind, V_line,
  V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  & (f22(V_trains_in_warning, V_train_counter_1, V_train_counter,
  V_secondary_wait_timer__initial_time, V_safety_mode_1, V_safety_mode,
  V_ret_1, V_opening_boom_timer__initial_time, V_number_of_booms,
  V_minimum_train_length, V_maximum_train_speed, V_maximum_train_length,
  V_max_number_of_trains, V_line_kind_1, V_line_kind, V_line,
  V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  & ($true & (f75(V_trains_in_warning, V_train_counter_1, V_train_counter,
  V_secondary_wait_timer__initial_time, V_safety_mode_1, V_safety_mode,
  V_ret_1, V_opening_boom_timer__initial_time, V_number_of_booms,
  V_minimum_train_length, V_maximum_train_speed, V_maximum_train_length,
  V_max_number_of_trains, V_line_kind_1, V_line_kind, V_line,
  V_last_train_in_warning_timer__initial_time, V_initialised,
  V_first_train_in_warning_timer__initial_time, V_cycle_duration,
  V_current_track_circuit_1, V_current_track_circuit_0,
  V_crossing_start_to_crossing_end, V_crossing_end_to_bdc_end,
  V_closing_boom_timer__initial_time, V_bijection_trains, V_bdc_state_1,
  V_bdc_state, V_bdc_start_to_crossing_start, V_adc_state_1, V_adc_state,
  V_adc_start_to_crossing_start, V_adc_end_to_crossing_start, V_TRAINS,
  V_BDCupdated_detector_1, V_BDCupdated_detector,
  V_BDCprevious_track_circuit_1, V_BDCprevious_track_circuit,
  V_BDCline_kind_1, V_BDCline_kind, V_BDCinitialised_1, V_BDCinitialised,
  V_BDCcurrent_track_circuit_1, V_BDCcurrent_track_circuit,
  V_BDCadc_or_bdc_kind_1, V_BDCadc_or_bdc_kind, V_ADCupdated_detector_1,
  V_ADCupdated_detector, V_ADCprevious_track_circuit_1,
  V_ADCprevious_track_circuit, V_ADCline_kind_1, V_ADCline_kind,
  V_ADCinitialised_1, V_ADCinitialised, V_ADCcurrent_track_circuit_1,
  V_ADCcurrent_track_circuit, V_ADCadc_or_bdc_kind_1, V_ADCadc_or_bdc_kind)
  & $true)))))) => ($false & $true))).
