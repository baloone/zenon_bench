;; Copyright 2012-2015 Consortium of the BWare ANR Project (ANR-12-INSE-0010)
;;	  	    <http://bware.lri.fr/>
;; Copyright 2012-2015 Cedric (CPR Team)
;;	  	    David DELAHAYE
;;	  	    <david.delahaye@cnam.fr>
;; Copyright 2012-2015 LRI (VALS team)
;;	  	    Sylvain CONCHON
;;	  	    <sylvain.conchon@lri.fr>
;; Copyright 2012-2015 Inria (Gallium, Deducteam)
;;	  	    Damien DOLIGEZ
;;	  	    <damien.doligez@inria.fr>
;; Copyright 2012-2015 Mitsubishi Electric R&D Centre Europe
;;	  	    David MENTRE
;;	  	    <d.mentre@fr.merce.mee.com>
;; Copyright 2012-2015 ClearSy
;;	  	    Thierry LECOMTE
;;	  	    <thierry.lecomte@clearsy.com>
;; Copyright 2012-2015 OCamlPro
;;	  	    Fabrice LE FESSANT
;;		    <fabrice.le_fessant@ocamlpro.com>
;;
;; This file is a free software.
;;
;; This software is governed by the CeCILL-B license under French law and 
;; abiding by the rules of distribution of free software.  
;; You can use, modify and/or redistribute the software under the terms of the 
;; CeCILL-B license as circulated by CEA, CNRS and INRIA at the following URL 
;; "http://www.cecill.info". 
;;
;; As a counterpart to the access to the source code and rights to copy,
;; modify and redistribute granted by the license, users are provided only
;; with a limited warranty and the software's author, the holder of the
;; economic rights, and the successive licensors have only limited liability. 
;;
;; In this respect, the user's attention is drawn to the risks associated
;; with loading, using, modifying and/or developing or reproducing the
;; software by the user in light of its specific status of free software,
;; that may mean that it is complicated to manipulate, and that also
;; therefore means that it is reserved for developers and experienced
;; professionals having in-depth computer knowledge. Users are therefore
;; encouraged to load and test the software's suitability as regards their
;; requirements in conditions enabling the security of their systems and/or 
;; data to be ensured and, more generally, to use and operate it in the 
;; same conditions as regards security. 
;;
;; The fact that you are presently reading this means that you have had
;; knowledge of the CeCILL-B license and that you accept its terms.
;;
;; ------------------------------------------------------------------------------
(set-logic UFNIA) 


(declare-sort uni 0)

(declare-sort ty 0)

(declare-fun sort (ty uni) Bool)

(declare-fun witness (ty) uni)

;; witness_sort
  (assert (forall ((a ty)) (sort a (witness a))))

(declare-fun int () ty)

(declare-fun real () ty)

(declare-fun bool () ty)

(declare-fun match_bool (ty Bool uni uni) uni)

;; match_bool_sort
  (assert
  (forall ((a ty))
  (forall ((x Bool) (x1 uni) (x2 uni)) (sort a (match_bool a x x1 x2)))))

;; match_bool_True
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni)) (=> (sort a z) (= (match_bool a true z z1) z)))))

;; match_bool_False
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_bool a false z z1) z1)))))

(declare-fun index_bool (Bool) Int)

;; index_bool_True
  (assert (= (index_bool true) 0))

;; index_bool_False
  (assert (= (index_bool false) 1))

;; bool_inversion
  (assert (forall ((u Bool)) (or (= u true) (= u false))))

;; CompatOrderMult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (=> (<= x y) (=> (<= 0 z) (<= (* x z) (* y z))))))

(declare-fun abs1 (Int) Int)

;; abs_def
  (assert
  (forall ((x Int)) (ite (<= 0 x) (= (abs1 x) x) (= (abs1 x) (- x)))))

;; Abs_le
  (assert
  (forall ((x Int) (y Int)) (= (<= (abs1 x) y) (and (<= (- y) x) (<= x y)))))

;; Abs_pos
  (assert (forall ((x Int)) (<= 0 (abs1 x))))

(declare-fun div1 (Int Int) Int)

(declare-fun mod1 (Int Int) Int)

;; Div_mod
  (assert
  (forall ((x Int) (y Int))
  (=> (not (= y 0)) (= x (+ (* y (div1 x y)) (mod1 x y))))))

;; Div_bound
  (assert
  (forall ((x Int) (y Int))
  (=> (and (<= 0 x) (< 0 y)) (and (<= 0 (div1 x y)) (<= (div1 x y) x)))))

;; Mod_bound
  (assert
  (forall ((x Int) (y Int))
  (=> (not (= y 0))
  (and (< (- (abs1 y)) (mod1 x y)) (< (mod1 x y) (abs1 y))))))

;; Div_sign_pos
  (assert
  (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< 0 y)) (<= 0 (div1 x y)))))

;; Div_sign_neg
  (assert
  (forall ((x Int) (y Int)) (=> (and (<= x 0) (< 0 y)) (<= (div1 x y) 0))))

;; Mod_sign_pos
  (assert
  (forall ((x Int) (y Int))
  (=> (and (<= 0 x) (not (= y 0))) (<= 0 (mod1 x y)))))

;; Mod_sign_neg
  (assert
  (forall ((x Int) (y Int))
  (=> (and (<= x 0) (not (= y 0))) (<= (mod1 x y) 0))))

;; Rounds_toward_zero
  (assert
  (forall ((x Int) (y Int))
  (=> (not (= y 0)) (<= (abs1 (* (div1 x y) y)) (abs1 x)))))

;; Div_1
  (assert (forall ((x Int)) (= (div1 x 1) x)))

;; Mod_1
  (assert (forall ((x Int)) (= (mod1 x 1) 0)))

;; Div_inf
  (assert
  (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y)) (= (div1 x y) 0))))

;; Mod_inf
  (assert
  (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y)) (= (mod1 x y) x))))

;; Div_mult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (! (=> (and (< 0 x) (and (<= 0 y) (<= 0 z)))
     (= (div1 (+ (* x y) z) x) (+ y (div1 z x)))) :pattern ((div1
                                                            (+ (* x y) z) x)) )))

;; Mod_mult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (! (=> (and (< 0 x) (and (<= 0 y) (<= 0 z)))
     (= (mod1 (+ (* x y) z) x) (mod1 z x))) :pattern ((mod1 (+ (* x y) z) x)) )))

(declare-sort set 1)

(declare-fun set1 (ty) ty)

(declare-sort enum_ETAT_AUTOMATE 0)

(declare-fun enum_ETAT_AUTOMATE1 () ty)

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (enum_ETAT_AUTOMATE (set enum_ETAT_AUTOMATE)) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun t2tb ((set enum_ETAT_AUTOMATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_ETAT_AUTOMATE))) (sort (set1 enum_ETAT_AUTOMATE1)
  (t2tb x))))

(declare-fun tb2t (uni) (set enum_ETAT_AUTOMATE))

;; BridgeL
  (assert
  (forall ((i (set enum_ETAT_AUTOMATE)))
  (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_ETAT_AUTOMATE1) j) (= (t2tb (tb2t j)) j)) :pattern (
  (t2tb (tb2t j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE)))
  (= (infix_eqeq enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2))
  (forall ((x enum_ETAT_AUTOMATE)) (= (mem1 x s1) (mem1 x s2))))))

;; infix ==_def
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni))
  (and
  (=> (infix_eqeq a s1 s2) (forall ((x uni)) (= (mem a x s1) (mem a x s2))))
  (=> (forall ((x uni)) (=> (sort a x) (= (mem a x s1) (mem a x s2))))
  (infix_eqeq a s1 s2))))))

;; extensionality
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni))
  (=> (sort (set1 a) s1)
  (=> (sort (set1 a) s2) (=> (infix_eqeq a s1 s2) (= s1 s2)))))))

(declare-fun subset (ty uni uni) Bool)

;; subset_def
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE)))
  (= (subset enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2))
  (forall ((x enum_ETAT_AUTOMATE)) (=> (mem1 x s1) (mem1 x s2))))))

;; subset_def
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni))
  (and
  (=> (subset a s1 s2) (forall ((x uni)) (=> (mem a x s1) (mem a x s2))))
  (=> (forall ((x uni)) (=> (sort a x) (=> (mem a x s1) (mem a x s2))))
  (subset a s1 s2))))))

;; subset_refl
  (assert (forall ((a ty)) (forall ((s uni)) (subset a s s))))

;; subset_trans
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (subset a s1 s2) (=> (subset a s2 s3) (subset a s1 s3))))))

(declare-fun empty (ty) uni)

;; empty_sort
  (assert (forall ((a ty)) (sort (set1 a) (empty a))))

(declare-fun empty1 () (set enum_ETAT_AUTOMATE))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE)))
  (= (is_empty enum_ETAT_AUTOMATE1 (t2tb s))
  (forall ((x enum_ETAT_AUTOMATE)) (not (mem1 x s))))))

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (is_empty enum_ETAT_AUTOMATE1 (t2tb empty1)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert (forall ((x enum_ETAT_AUTOMATE)) (not (mem1 x empty1))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (enum_ETAT_AUTOMATE
  (set enum_ETAT_AUTOMATE)) (set enum_ETAT_AUTOMATE))

;; add_def1
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (forall ((s (set enum_ETAT_AUTOMATE)))
  (= (mem1 x (add1 y s)) (or (= x y) (mem1 x s))))))

;; add_def1
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort a y)
  (forall ((s uni)) (= (mem a x (add a y s)) (or (= x y) (mem a x s)))))))))

(declare-fun remove (ty uni uni) uni)

;; remove_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 uni)) (sort (set1 a) (remove a x x1)))))

(declare-fun t2tb1 (enum_ETAT_AUTOMATE) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_ETAT_AUTOMATE)) (sort enum_ETAT_AUTOMATE1 (t2tb1 x))))

(declare-fun tb2t1 (uni) enum_ETAT_AUTOMATE)

;; BridgeL
  (assert
  (forall ((i enum_ETAT_AUTOMATE))
  (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_ETAT_AUTOMATE1 j) (= (t2tb1 (tb2t1 j)) j)) :pattern (
  (t2tb1 (tb2t1 j))) )))

;; remove_def1
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE)
  (s (set enum_ETAT_AUTOMATE)))
  (= (mem1 x (tb2t (remove enum_ETAT_AUTOMATE1 (t2tb1 y) (t2tb s))))
  (and (not (= x y)) (mem1 x s)))))

;; remove_def1
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni) (s uni))
  (=> (sort a x)
  (=> (sort a y)
  (= (mem a x (remove a y s)) (and (not (= x y)) (mem a x s))))))))

;; add_remove
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s (set enum_ETAT_AUTOMATE)))
  (=> (mem1 x s)
  (= (add1 x (tb2t (remove enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s (set enum_ETAT_AUTOMATE)))
  (= (tb2t (remove enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb (add1 x s)))) 
  (tb2t (remove enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb s))))))

;; remove_add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni)) (= (remove a x (add a x s)) (remove a x s)))))

;; subset_remove
  (assert
  (forall ((a ty)) (forall ((x uni) (s uni)) (subset a (remove a x s) s))))

(declare-fun union (ty uni uni) uni)

;; union_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 uni)) (sort (set1 a) (union a x x1)))))

(declare-fun union1 ((set enum_ETAT_AUTOMATE)
  (set enum_ETAT_AUTOMATE)) (set enum_ETAT_AUTOMATE))

;; union_def1
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE))
  (x enum_ETAT_AUTOMATE))
  (= (mem1 x (union1 s1 s2)) (or (mem1 x s1) (mem1 x s2)))))

;; union_def1
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (x uni))
  (= (mem a x (union a s1 s2)) (or (mem a x s1) (mem a x s2))))))

(declare-fun inter (ty uni uni) uni)

;; inter_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 uni)) (sort (set1 a) (inter a x x1)))))

;; inter_def1
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE))
  (x enum_ETAT_AUTOMATE))
  (= (mem1 x (tb2t (inter enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2))))
  (and (mem1 x s1) (mem1 x s2)))))

;; inter_def1
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (x uni))
  (= (mem a x (inter a s1 s2)) (and (mem a x s1) (mem a x s2))))))

(declare-fun diff (ty uni uni) uni)

;; diff_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (diff a x x1)))))

;; diff_def1
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE))
  (x enum_ETAT_AUTOMATE))
  (= (mem1 x (tb2t (diff enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2))))
  (and (mem1 x s1) (not (mem1 x s2))))))

;; diff_def1
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (x uni))
  (= (mem a x (diff a s1 s2)) (and (mem a x s1) (not (mem a x s2)))))))

;; subset_diff
  (assert
  (forall ((a ty)) (forall ((s1 uni) (s2 uni)) (subset a (diff a s1 s2) s1))))

(declare-fun choose (ty uni) uni)

;; choose_sort
  (assert (forall ((a ty)) (forall ((x uni)) (sort a (choose a x)))))

;; choose_def
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE)))
  (=> (not (is_empty enum_ETAT_AUTOMATE1 (t2tb s))) (mem1
  (tb2t1 (choose enum_ETAT_AUTOMATE1 (t2tb s))) s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert
  (forall ((x enum_ETAT_AUTOMATE)) (mem1 x (tb2t (all enum_ETAT_AUTOMATE1)))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

(declare-fun t2tb2 (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb2 x))))

(declare-fun tb2t2 (uni) Bool)

;; BridgeL
  (assert
  (forall ((i Bool)) (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb2 (tb2t2 j)) j)) :pattern ((t2tb2 (tb2t2 j))) )))

(declare-fun t2tb3 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb3 x))))

(declare-fun tb2t3 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool))) (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb3 (tb2t3 j)) j)) :pattern ((t2tb3
                                                                 (tb2t3 j))) )))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb2 x) (t2tb3 b_bool))))

(declare-fun integer () (set Int))

(declare-fun t2tb4 ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int))) (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb4 (tb2t4 j)) j) :pattern ((t2tb4 (tb2t4 j))) )))

(declare-fun t2tb5 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb5 x))))

(declare-fun tb2t5 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb5 (tb2t5 j)) j) :pattern ((t2tb5 (tb2t5 j))) )))

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb5 x) (t2tb4 integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert
  (forall ((x Int)) (= (mem int (t2tb5 x) (t2tb4 natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert
  (forall ((x Int)) (= (mem int (t2tb5 x) (t2tb4 natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb5 x) (t2tb4 nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb5 x) (t2tb4 nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb5 x) (t2tb4 bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb5 x) (t2tb4 (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb5 x) (t2tb4 (mk a b)))) )))

;; interval_empty
  (assert
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t4 (empty int))))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t4 (add int (t2tb5 b) (t2tb4 (mk a (- b 1)))))))))

(declare-fun power (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power a x)))))

;; mem_power
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni))
  (! (= (mem (set1 a) x (power a y)) (subset a x y)) :pattern ((mem (set1 a)
  x (power a y))) ))))

(declare-fun non_empty_power (ty uni) uni)

;; non_empty_power_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (non_empty_power a x)))))

(declare-fun t2tb6 ((set (set enum_ETAT_AUTOMATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set enum_ETAT_AUTOMATE)))) (sort
  (set1 (set1 enum_ETAT_AUTOMATE1)) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set (set enum_ETAT_AUTOMATE)))

;; BridgeL
  (assert
  (forall ((i (set (set enum_ETAT_AUTOMATE))))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 enum_ETAT_AUTOMATE1)) j) (= (t2tb6 (tb2t6 j)) j)) :pattern (
  (t2tb6 (tb2t6 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set enum_ETAT_AUTOMATE)) (y (set enum_ETAT_AUTOMATE)))
  (! (= (mem (set1 enum_ETAT_AUTOMATE1) (t2tb x)
     (non_empty_power enum_ETAT_AUTOMATE1 (t2tb y)))
     (and (subset enum_ETAT_AUTOMATE1 (t2tb x) (t2tb y)) (not (= x empty1)))) :pattern ((mem
  (set1 enum_ETAT_AUTOMATE1) (t2tb x)
  (non_empty_power enum_ETAT_AUTOMATE1 (t2tb y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni))
  (! (=> (sort (set1 a) x)
     (= (mem (set1 a) x (non_empty_power a y))
     (and (subset a x y) (not (= x (empty a)))))) :pattern ((mem
  (set1 a) x (non_empty_power a y))) ))))

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun Tuple2 (ty ty uni uni) uni)

;; Tuple2_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni) (x1 uni)) (sort (tuple21 a1 a) (Tuple2 a1 a x x1)))))

(declare-fun Tuple2_proj_1 (ty ty uni) uni)

;; Tuple2_proj_1_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni)) (sort a1 (Tuple2_proj_1 a1 a x)))))

;; Tuple2_proj_1_def
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((u uni) (u1 uni))
  (=> (sort a1 u) (= (Tuple2_proj_1 a1 a (Tuple2 a1 a u u1)) u)))))

(declare-fun Tuple2_proj_2 (ty ty uni) uni)

;; Tuple2_proj_2_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni)) (sort a (Tuple2_proj_2 a1 a x)))))

;; Tuple2_proj_2_def
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((u uni) (u1 uni))
  (=> (sort a u1) (= (Tuple2_proj_2 a1 a (Tuple2 a1 a u u1)) u1)))))

;; tuple2_inversion
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((u uni))
  (=> (sort (tuple21 a1 a) u)
  (= u (Tuple2 a1 a (Tuple2_proj_1 a1 a u) (Tuple2_proj_2 a1 a u)))))))

(declare-fun relation (ty ty uni uni) uni)

;; relation_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (relation b a x x1)))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_ETAT_AUTOMATE)))
  (and
  (=> (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (relation enum_ETAT_AUTOMATE1 a s (t2tb t)))
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) f) (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) f) (and (mem a x s) (mem1 y t)))))
  (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (relation enum_ETAT_AUTOMATE1 a s (t2tb t))))))))

(declare-fun t2tb7 ((set (set (tuple2 enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))))
  (sort (set1 (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)))
  (t2tb7 x))))

(declare-fun tb2t7 (uni) (set (set (tuple2 enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1))) j)
     (= (t2tb7 (tb2t7 j)) j)) :pattern ((t2tb7 (tb2t7 j))) )))

(declare-fun t2tb8 ((set (tuple2 enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))) (sort
  (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)) (t2tb8 x))))

(declare-fun tb2t8 (uni) (set (tuple2 enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE))))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)) j)
     (= (t2tb8 (tb2t8 j)) j)) :pattern ((t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 ((tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE))) (sort
  (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1) (t2tb9 x))))

(declare-fun tb2t9 (uni) (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1) j)
     (= (t2tb9 (tb2t9 j)) j)) :pattern ((t2tb9 (tb2t9 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (s (set enum_ETAT_AUTOMATE)) (t (set enum_ETAT_AUTOMATE)))
  (= (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)) (t2tb8 f)
  (relation enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s) (t2tb t)))
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (t2tb8 f)) (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_ETAT_AUTOMATE)) (t uni))
  (and
  (=> (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (relation b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) f) (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) f) (and (mem1 x s) (mem b y t)))))
  (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (relation b enum_ETAT_AUTOMATE1 (t2tb s) t)))))))

;; mem_relation
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (and
  (=> (mem (set1 (tuple21 a b)) f (relation b a s t))
  (forall ((x uni) (y uni))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t)))))
  (=>
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y)
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t))))))
  (mem (set1 (tuple21 a b)) f (relation b a s t)))))))

(declare-fun image (ty ty uni uni) uni)

;; image_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 b) (image b a x x1)))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom1 uni) (y enum_ETAT_AUTOMATE))
  (! (and
     (=> (mem1 y (tb2t (image enum_ETAT_AUTOMATE1 a r dom1)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom1) (mem (tuple21 a enum_ETAT_AUTOMATE1)
     (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom1) (mem (tuple21 a enum_ETAT_AUTOMATE1)
     (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) r))) (mem1 y
     (tb2t (image enum_ETAT_AUTOMATE1 a r dom1))))) :pattern ((mem1
  y (tb2t (image enum_ETAT_AUTOMATE1 a r dom1)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (dom1 (set enum_ETAT_AUTOMATE)) (y enum_ETAT_AUTOMATE))
  (! (= (mem1 y
     (tb2t
     (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 r) (t2tb dom1))))
     (exists ((x enum_ETAT_AUTOMATE))
     (and (mem1 x dom1) (mem
     (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
     (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
     (t2tb8 r))))) :pattern ((mem1
  y
  (tb2t
  (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 r) (t2tb dom1))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set enum_ETAT_AUTOMATE)) (y uni))
  (! (= (mem b y (image b enum_ETAT_AUTOMATE1 r (t2tb dom1)))
     (exists ((x enum_ETAT_AUTOMATE))
     (and (mem1 x dom1) (mem (tuple21 enum_ETAT_AUTOMATE1 b)
     (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) r)))) :pattern ((mem
  b y (image b enum_ETAT_AUTOMATE1 r (t2tb dom1)))) ))))

;; mem_image
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (dom1 uni) (y uni))
  (! (and
     (=> (mem b y (image b a r dom1))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom1) (mem (tuple21 a b) (Tuple2 a b x y) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom1) (mem (tuple21 a b) (Tuple2 a b x y) r))) (mem b y
     (image b a r dom1)))) :pattern ((mem
  b y (image b a r dom1))) ))))

;; image_union
  (assert
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t (image enum_ETAT_AUTOMATE1 a r (union a s t))) (union1
                                                          (tb2t
                                                          (image
                                                          enum_ETAT_AUTOMATE1
                                                          a r s))
                                                          (tb2t
                                                          (image
                                                          enum_ETAT_AUTOMATE1
                                                          a r t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (s (set enum_ETAT_AUTOMATE)) (t (set enum_ETAT_AUTOMATE)))
  (= (tb2t
     (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 r)
     (t2tb (union1 s t)))) (union1
                           (tb2t
                           (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1
                           (t2tb8 r) (t2tb s)))
                           (tb2t
                           (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1
                           (t2tb8 r) (t2tb t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set enum_ETAT_AUTOMATE)) (t (set enum_ETAT_AUTOMATE)))
  (= (image b enum_ETAT_AUTOMATE1 r (t2tb (union1 s t))) (union b
                                                         (image b
                                                         enum_ETAT_AUTOMATE1
                                                         r (t2tb s))
                                                         (image b
                                                         enum_ETAT_AUTOMATE1
                                                         r (t2tb t)))))))

;; image_union
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (s uni) (t uni))
  (= (image b a r (union a s t)) (union b (image b a r s) (image b a r t))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom1 uni) (x uni))
  (= (tb2t (image enum_ETAT_AUTOMATE1 a r (add a x dom1))) (union1
                                                           (tb2t
                                                           (image
                                                           enum_ETAT_AUTOMATE1
                                                           a r
                                                           (add a x
                                                           (empty a))))
                                                           (tb2t
                                                           (image
                                                           enum_ETAT_AUTOMATE1
                                                           a r dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (dom1 (set enum_ETAT_AUTOMATE)) (x enum_ETAT_AUTOMATE))
  (= (tb2t
     (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 r)
     (t2tb (add1 x dom1)))) (union1
                            (tb2t
                            (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1
                            (t2tb8 r) (t2tb (add1 x empty1))))
                            (tb2t
                            (image enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1
                            (t2tb8 r) (t2tb dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set enum_ETAT_AUTOMATE)) (x enum_ETAT_AUTOMATE))
  (= (image b enum_ETAT_AUTOMATE1 r (t2tb (add1 x dom1))) (union b
                                                          (image b
                                                          enum_ETAT_AUTOMATE1
                                                          r
                                                          (t2tb
                                                          (add1 x empty1)))
                                                          (image b
                                                          enum_ETAT_AUTOMATE1
                                                          r (t2tb dom1)))))))

;; image_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (dom1 uni) (x uni))
  (= (image b a r (add a x dom1)) (union b (image b a r (add a x (empty a)))
                                  (image b a r dom1))))))

(declare-fun infix_plmngt (ty ty uni uni) uni)

;; infix +->_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_plmngt b a x x1)))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_ETAT_AUTOMATE)))
  (and
  (=> (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t)))
  (and
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) f) (and (mem a x s) (mem1 y t))))
  (forall ((x uni) (y1 enum_ETAT_AUTOMATE) (y2 enum_ETAT_AUTOMATE))
  (=>
  (and (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y1)) f) (mem
  (tuple21 a enum_ETAT_AUTOMATE1) (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y2))
  f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) f) (and (mem a x s) (mem1 y t)))))
  (forall ((x uni) (y1 enum_ETAT_AUTOMATE) (y2 enum_ETAT_AUTOMATE))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y1)) f) (mem
  (tuple21 a enum_ETAT_AUTOMATE1) (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y2))
  f)) (= y1 y2))))) (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (s (set enum_ETAT_AUTOMATE)) (t (set enum_ETAT_AUTOMATE)))
  (= (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)) (t2tb8 f)
  (infix_plmngt enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s) (t2tb t)))
  (and
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (t2tb8 f)) (and (mem1 x s) (mem1 y t))))
  (forall ((x enum_ETAT_AUTOMATE) (y1 enum_ETAT_AUTOMATE)
  (y2 enum_ETAT_AUTOMATE))
  (=>
  (and (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y1))
  (t2tb8 f)) (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y2))
  (t2tb8 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_ETAT_AUTOMATE)) (t uni))
  (and
  (=> (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (and
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) f) (and (mem1 x s) (mem b y t))))
  (forall ((x enum_ETAT_AUTOMATE) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y1) f) (mem
  (tuple21 enum_ETAT_AUTOMATE1 b) (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y2)
  f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) f) (and (mem1 x s) (mem b y t)))))
  (forall ((x enum_ETAT_AUTOMATE) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y1) f) (mem
  (tuple21 enum_ETAT_AUTOMATE1 b) (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y2)
  f)) (= y1 y2)))))) (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)))))))

;; mem_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (and
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (and
  (forall ((x uni) (y uni))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t))))
  (forall ((x uni) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 a b) (Tuple2 a b x y1) f) (mem (tuple21 a b)
  (Tuple2 a b x y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y)
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t))))))
  (forall ((x uni) (y1 uni) (y2 uni))
  (=> (sort a x)
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 a b) (Tuple2 a b x y1) f) (mem (tuple21 a b)
  (Tuple2 a b x y2) f)) (= y1 y2))))))) (mem (set1 (tuple21 a b)) f
  (infix_plmngt b a s t)))))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_ETAT_AUTOMATE)) (t uni)
  (x enum_ETAT_AUTOMATE) (y uni))
  (=> (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) f) (mem1 x s))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_ETAT_AUTOMATE)) (x uni)
  (y enum_ETAT_AUTOMATE))
  (=> (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t)))
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) f) (mem1 y t))))))

;; range_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem b y t))))))

;; function_extend_range
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (u uni))
  (=> (subset b t u)
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_plmngt b a s u)))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_ETAT_AUTOMATE))
  (u (set enum_ETAT_AUTOMATE)))
  (=> (subset enum_ETAT_AUTOMATE1 (t2tb u) (t2tb t))
  (=> (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t)))
  (=>
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (u uni))
  (=> (subset b u t)
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=>
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y) (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem b y u)))))
  (mem (set1 (tuple21 a b)) f (infix_plmngt b a s u))))))))

(declare-fun inverse (ty ty uni) uni)

;; inverse_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni)) (sort (set1 (tuple21 b a)) (inverse b a x)))))

;; Inverse_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni))
  (forall ((x uni) (y uni))
  (= (mem (tuple21 b a) (Tuple2 b a y x) (inverse b a r)) (mem (tuple21 a b)
  (Tuple2 a b x y) r))))))

(declare-fun dom (ty ty uni) uni)

;; dom_sort
  (assert
  (forall ((a ty) (b ty)) (forall ((x uni)) (sort (set1 a) (dom b a x)))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x enum_ETAT_AUTOMATE))
  (and
  (=> (mem1 x (tb2t (dom b enum_ETAT_AUTOMATE1 r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) r)) (mem1 x
  (tb2t (dom b enum_ETAT_AUTOMATE1 r)))))))))

;; dom_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni))
  (forall ((x uni))
  (and
  (=> (mem a x (dom b a r))
  (exists ((y uni)) (and (sort b y) (mem (tuple21 a b) (Tuple2 a b x y) r))))
  (=> (exists ((y uni)) (mem (tuple21 a b) (Tuple2 a b x y) r)) (mem a x
  (dom b a r))))))))

(declare-fun ran (ty ty uni) uni)

;; ran_sort
  (assert
  (forall ((a ty) (b ty)) (forall ((x uni)) (sort (set1 b) (ran b a x)))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y enum_ETAT_AUTOMATE))
  (and
  (=> (mem1 y (tb2t (ran enum_ETAT_AUTOMATE1 a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) r)) (mem1 y
  (tb2t (ran enum_ETAT_AUTOMATE1 a r)))))))))

;; ran_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni))
  (forall ((y uni))
  (and
  (=> (mem b y (ran b a r))
  (exists ((x uni)) (and (sort a x) (mem (tuple21 a b) (Tuple2 a b x y) r))))
  (=> (exists ((x uni)) (mem (tuple21 a b) (Tuple2 a b x y) r)) (mem b y
  (ran b a r))))))))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t
     (dom b enum_ETAT_AUTOMATE1 (empty (tuple21 enum_ETAT_AUTOMATE1 b)))) 
  empty1)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x enum_ETAT_AUTOMATE) (y uni))
  (= (tb2t
     (dom b enum_ETAT_AUTOMATE1
     (add (tuple21 enum_ETAT_AUTOMATE1 b)
     (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) f))) (add1 x
                                                     (tb2t
                                                     (dom b
                                                     enum_ETAT_AUTOMATE1 f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (= (tb2t
     (dom b enum_ETAT_AUTOMATE1
     (add (tuple21 enum_ETAT_AUTOMATE1 b)
     (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
     (empty (tuple21 enum_ETAT_AUTOMATE1 b))))) (add1 x empty1)))))

;; dom_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b)))) 
  (add a x (empty a))))))

(declare-fun infix_mnmngt (ty ty uni uni) uni)

;; infix -->_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_mnmngt b a x x1)))))

;; mem_total_functions
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 a) s)
  (= (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (= (dom b a f) s)))))))

;; total_function_is_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (! (=> (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem
     (set1 (tuple21 a b)) f (infix_plmngt b a s t))) :pattern ((mem
  (set1 (tuple21 a b)) f (infix_mnmngt b a s t))) ))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set enum_ETAT_AUTOMATE)) (x uni)
  (y enum_ETAT_AUTOMATE))
  (=> (and (mem a x s) (mem1 y t)) (mem
  (set1 (tuple21 a enum_ETAT_AUTOMATE1))
  (add (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y))
  (empty (tuple21 a enum_ETAT_AUTOMATE1)))
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE)) (t (set enum_ETAT_AUTOMATE))
  (x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (=> (and (mem1 x s) (mem1 y t)) (mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1))
  (add (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (empty (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)))
  (infix_plmngt enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set enum_ETAT_AUTOMATE)) (t uni) (x enum_ETAT_AUTOMATE)
  (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 b))
  (add (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
  (empty (tuple21 enum_ETAT_AUTOMATE1 b)))
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (x uni) (y uni))
  (=> (and (mem a x s) (mem b y t)) (mem (set1 (tuple21 a b))
  (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b)))
  (infix_plmngt b a s t))))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y enum_ETAT_AUTOMATE)) (! (mem
  (set1 (tuple21 a enum_ETAT_AUTOMATE1))
  (add (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y))
  (empty (tuple21 a enum_ETAT_AUTOMATE1)))
  (infix_mnmngt enum_ETAT_AUTOMATE1 a (add a x (empty a))
  (t2tb (add1 y empty1)))) :pattern ((add (tuple21 a enum_ETAT_AUTOMATE1)
                                     (Tuple2 a enum_ETAT_AUTOMATE1 x
                                     (t2tb1 y))
                                     (empty (tuple21 a enum_ETAT_AUTOMATE1)))) ))))

;; singleton_is_function
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE)) (! (mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1))
  (add (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (empty (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)))
  (infix_mnmngt enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1
  (t2tb (add1 x empty1)) (t2tb (add1 y empty1)))) :pattern ((tb2t8
                                                            (add
                                                            (tuple21
                                                            enum_ETAT_AUTOMATE1
                                                            enum_ETAT_AUTOMATE1)
                                                            (Tuple2
                                                            enum_ETAT_AUTOMATE1
                                                            enum_ETAT_AUTOMATE1
                                                            (t2tb1 x)
                                                            (t2tb1 y))
                                                            (empty
                                                            (tuple21
                                                            enum_ETAT_AUTOMATE1
                                                            enum_ETAT_AUTOMATE1))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x enum_ETAT_AUTOMATE) (y uni)) (! (mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 b))
  (add (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
  (empty (tuple21 enum_ETAT_AUTOMATE1 b)))
  (infix_mnmngt b enum_ETAT_AUTOMATE1 (t2tb (add1 x empty1))
  (add b y (empty b)))) :pattern ((add (tuple21 enum_ETAT_AUTOMATE1 b)
                                  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
                                  (empty (tuple21 enum_ETAT_AUTOMATE1 b)))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni)) (! (mem (set1 (tuple21 a b))
  (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b)))
  (infix_mnmngt b a (add a x (empty a)) (add b y (empty b)))) :pattern (
  (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b)))) ))))

(declare-fun apply (ty ty uni uni) uni)

;; apply_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort b (apply b a x x1)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_ETAT_AUTOMATE)) (t uni)
  (a enum_ETAT_AUTOMATE))
  (=>
  (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)) (mem1 a
  (tb2t (dom b enum_ETAT_AUTOMATE1 f)))) (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 a)
  (apply b enum_ETAT_AUTOMATE1 f (t2tb1 a))) f)))))

;; apply_def0
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem a a1
  (dom b a f))) (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_ETAT_AUTOMATE)) (t uni)
  (a enum_ETAT_AUTOMATE))
  (=>
  (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_mnmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)) (mem1 a s)) (mem
  (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 a)
  (apply b enum_ETAT_AUTOMATE1 f (t2tb1 a))) f)))))

;; apply_def1
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=> (and (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem a a1 s))
  (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def2
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni) (b1 uni))
  (=> (sort b b1)
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem (tuple21 a b)
  (Tuple2 a b a1 b1) f)) (= (apply b a f a1) b1))))))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b))) x) y)))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set enum_ETAT_AUTOMATE)))
  (! (=>
     (and (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
     (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t))) (mem a x
     (dom enum_ETAT_AUTOMATE1 a f))) (mem1
     (tb2t1 (apply enum_ETAT_AUTOMATE1 a f x)) t)) :pattern ((mem
  (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t)))
  (tb2t1 (apply enum_ETAT_AUTOMATE1 a f x))) ))))

;; apply_range
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (f (set (tuple2 enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE))) (s (set enum_ETAT_AUTOMATE))
  (t (set enum_ETAT_AUTOMATE)))
  (! (=>
     (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1))
     (t2tb8 f)
     (infix_plmngt enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s) (t2tb t)))
     (mem1 x (tb2t (dom enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f)))))
     (mem1
     (tb2t1
     (apply enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f) (t2tb1 x))) t)) :pattern ((mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)) (t2tb8 f)
  (infix_plmngt enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s) (t2tb t)))
  (tb2t1 (apply enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f) (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x enum_ETAT_AUTOMATE) (f uni) (s (set enum_ETAT_AUTOMATE))
  (t uni))
  (! (=>
     (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
     (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)) (mem1 x
     (tb2t (dom b enum_ETAT_AUTOMATE1 f)))) (mem b
     (apply b enum_ETAT_AUTOMATE1 f (t2tb1 x)) t)) :pattern ((mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (apply b enum_ETAT_AUTOMATE1 f (t2tb1 x))) ))))

;; apply_range
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (f uni) (s uni) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem a x
     (dom b a f))) (mem b (apply b a f x) t)) :pattern ((mem
  (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (apply b a f x)) ))))

(declare-fun semicolon (ty ty ty uni uni) uni)

;; semicolon_sort
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a c))
  (semicolon c b a x x1)))))

;; semicolon_def
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (z uni) (p uni) (q uni))
  (and
  (=> (mem (tuple21 a c) (Tuple2 a c x z) (semicolon c b a p q))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 a b) (Tuple2 a b x y) p) (mem (tuple21 b c)
  (Tuple2 b c y z) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 a b) (Tuple2 a b x y) p) (mem (tuple21 b c)
  (Tuple2 b c y z) q))) (mem (tuple21 a c) (Tuple2 a c x z)
  (semicolon c b a p q)))))))

(declare-fun direct_product (ty ty ty uni uni) uni)

;; direct_product_sort
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a (tuple21 b c)))
  (direct_product c b a x x1)))))

;; direct_product_def
  (assert
  (forall ((t ty) (u ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (! (=> (sort (tuple21 t (tuple21 u v)) e)
     (and
     (=> (mem (tuple21 t (tuple21 u v)) e (direct_product v u t r1 r2))
     (exists ((x uni) (y uni) (z uni))
     (and (sort t x)
     (and (sort u y)
     (and (sort v z)
     (and (= (Tuple2 t (tuple21 u v) x (Tuple2 u v y z)) e)
     (and (mem (tuple21 t u) (Tuple2 t u x y) r1) (mem (tuple21 t v)
     (Tuple2 t v x z) r2))))))))
     (=>
     (exists ((x uni) (y uni) (z uni))
     (and (= (Tuple2 t (tuple21 u v) x (Tuple2 u v y z)) e)
     (and (mem (tuple21 t u) (Tuple2 t u x y) r1) (mem (tuple21 t v)
     (Tuple2 t v x z) r2)))) (mem (tuple21 t (tuple21 u v)) e
     (direct_product v u t r1 r2))))) :pattern ((mem
  (tuple21 t (tuple21 u v)) e (direct_product v u t r1 r2))) ))))

(declare-fun parallel_product (ty ty ty ty uni uni) uni)

;; parallel_product_sort
  (assert
  (forall ((a ty) (b ty) (c ty) (d ty))
  (forall ((x uni) (x1 uni)) (sort
  (set1 (tuple21 (tuple21 a c) (tuple21 b d)))
  (parallel_product d c b a x x1)))))

;; parallel_product_def
  (assert
  (forall ((t ty) (u ty) (v ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort (tuple21 (tuple21 t v) (tuple21 u w)) e)
  (and
  (=> (mem (tuple21 (tuple21 t v) (tuple21 u w)) e
  (parallel_product w v u t r1 r2))
  (exists ((x uni) (y uni) (z uni) (a uni))
  (and (sort t x)
  (and (sort v y)
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 u w) (Tuple2 t v x y) (Tuple2 u w z a)) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem (tuple21 v w)
  (Tuple2 v w y a) r2)))))))))
  (=>
  (exists ((x uni) (y uni) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 u w) (Tuple2 t v x y) (Tuple2 u w z a)) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem (tuple21 v w)
  (Tuple2 v w y a) r2)))) (mem (tuple21 (tuple21 t v) (tuple21 u w)) e
  (parallel_product w v u t r1 r2))))))))

;; semicolon_dom
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((f uni) (g uni)) (subset a (dom c a (semicolon c b a f g))
  (dom b a f)))))

;; semicolon_is_function
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((f uni) (g uni) (s uni) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple21 b c)) g (infix_plmngt c b t u))) (mem (set1 (tuple21 a c))
  (semicolon c b a f g) (infix_plmngt c a s u))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set enum_ETAT_AUTOMATE))
  (u uni))
  (=>
  (and (mem (set1 (tuple21 a enum_ETAT_AUTOMATE1)) f
  (infix_plmngt enum_ETAT_AUTOMATE1 a s (t2tb t)))
  (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 c)) g
  (infix_plmngt c enum_ETAT_AUTOMATE1 (t2tb t) u))
  (and (mem a x (dom enum_ETAT_AUTOMATE1 a f)) (mem1
  (tb2t1 (apply enum_ETAT_AUTOMATE1 a f x))
  (tb2t (dom c enum_ETAT_AUTOMATE1 g))))))
  (= (apply c a (semicolon c enum_ETAT_AUTOMATE1 a f g) x) (apply c
                                                           enum_ETAT_AUTOMATE1
                                                           g
                                                           (apply
                                                           enum_ETAT_AUTOMATE1
                                                           a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x enum_ETAT_AUTOMATE) (f (set (tuple2 enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE))) (g uni) (s (set enum_ETAT_AUTOMATE))
  (t (set enum_ETAT_AUTOMATE)) (u uni))
  (=>
  (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1))
  (t2tb8 f)
  (infix_plmngt enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s) (t2tb t)))
  (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 c)) g
  (infix_plmngt c enum_ETAT_AUTOMATE1 (t2tb t) u))
  (and (mem1 x
  (tb2t (dom enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f)))) (mem1
  (tb2t1 (apply enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f) (t2tb1 x)))
  (tb2t (dom c enum_ETAT_AUTOMATE1 g))))))
  (= (apply c enum_ETAT_AUTOMATE1
     (semicolon c enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f) g)
     (t2tb1 x)) (apply c enum_ETAT_AUTOMATE1 g
                (apply enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb8 f)
                (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x enum_ETAT_AUTOMATE) (f uni) (g uni)
  (s (set enum_ETAT_AUTOMATE)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t (dom b enum_ETAT_AUTOMATE1 f))) (mem b
  (apply b enum_ETAT_AUTOMATE1 f (t2tb1 x)) (dom c b g)))))
  (= (apply c enum_ETAT_AUTOMATE1 (semicolon c b enum_ETAT_AUTOMATE1 f g)
     (t2tb1 x)) (apply c b g (apply b enum_ETAT_AUTOMATE1 f (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem a x (dom b a f)) (mem b (apply b a f x) (dom c b g)))))
  (= (apply c a (semicolon c b a f g) x) (apply c b g (apply b a f x)))))))

(declare-fun infix_gtplgt (ty ty uni uni) uni)

;; infix >+>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_gtplgt b a x x1)))))

;; mem_partial_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtplgt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple21 b a)) (inverse b a f) (infix_plmngt a b t s)))))))

(declare-fun infix_gtmngt (ty ty uni uni) uni)

;; infix >->_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_gtmngt b a x x1)))))

;; mem_total_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_mnmngt b a s t)))))))

;; mem_total_injection_alt
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem
  (set1 (tuple21 b a)) (inverse b a f) (infix_plmngt a b t s)))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_ETAT_AUTOMATE)) (t uni))
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (=> (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_gtmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=>
  (= (apply b enum_ETAT_AUTOMATE1 f (t2tb1 x)) (apply b enum_ETAT_AUTOMATE1 f
                                               (t2tb1 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort a y)
  (=> (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t))
  (=> (mem a x s)
  (=> (mem a y s) (=> (= (apply b a f x) (apply b a f y)) (= x y)))))))))))

(declare-fun infix_plmngtgt (ty ty uni uni) uni)

;; infix +->>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_plmngtgt b a x x1)))))

;; mem_partial_surjection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 b) t)
  (= (mem (set1 (tuple21 a b)) f (infix_plmngtgt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (= (ran b a f) t)))))))

(declare-fun infix_mnmngtgt (ty ty uni uni) uni)

;; infix -->>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_mnmngtgt b a x x1)))))

;; mem_total_surjection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_mnmngtgt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngtgt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_mnmngt b a s t)))))))

(declare-fun infix_gtplgtgt (ty ty uni uni) uni)

;; infix >+>>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_gtplgtgt b a x x1)))))

;; mem_partial_bijection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtplgtgt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_plmngtgt b a s t)))))))

(declare-fun infix_gtmngtgt (ty ty uni uni) uni)

;; infix >->>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_gtmngtgt b a x x1)))))

;; mem_total_bijection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtmngtgt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_mnmngtgt b a s t)))))))

(declare-fun id (ty uni) uni)

;; id_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (tuple21 a a)) (id a x)))))

;; id_def
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE)
  (s (set enum_ETAT_AUTOMATE)))
  (= (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (id enum_ETAT_AUTOMATE1 (t2tb s))) (and (mem1 x s) (= x y)))))

;; id_def
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni) (s uni))
  (=> (sort a x)
  (=> (sort a y)
  (= (mem (tuple21 a a) (Tuple2 a a x y) (id a s)) (and (mem a x s) (= x y))))))))

;; id_dom
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (sort (set1 a) s) (= (dom a a (id a s)) s)))))

;; id_ran
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (sort (set1 a) s) (= (ran a a (id a s)) s)))))

;; id_fun
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 (tuple21 a a)) (id a s)
  (infix_plmngt a a s s)))))

;; id_total_fun
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 (tuple21 a a)) (id a s)
  (infix_mnmngt a a s s)))))

(declare-fun seq_length (ty Int uni) uni)

;; seq_length_sort
  (assert
  (forall ((a ty))
  (forall ((x Int) (x1 uni)) (sort (set1 (set1 (tuple21 int a)))
  (seq_length a x x1)))))

;; seq_length_def
  (assert
  (forall ((a ty))
  (forall ((n Int) (s uni))
  (= (seq_length a n s) (infix_mnmngt a int (t2tb4 (mk 1 n)) s)))))

;; length_uniq
  (assert
  (forall ((a ty))
  (forall ((n1 Int) (n2 Int) (s1 uni) (s2 uni) (r uni))
  (=> (and (<= 0 n1) (mem (set1 (tuple21 int a)) r (seq_length a n1 s1)))
  (=> (and (<= 0 n2) (mem (set1 (tuple21 int a)) r (seq_length a n2 s2)))
  (= n1 n2))))))

(declare-fun size (ty uni) Int)

;; size_def
  (assert
  (forall ((a ty))
  (forall ((n Int) (s uni) (r uni))
  (=> (and (<= 0 n) (mem (set1 (tuple21 int a)) r (seq_length a n s)))
  (= (size a r) n)))))

(declare-fun seq (ty uni) uni)

;; seq_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple21 int a))) (seq a x)))))

;; seq_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (r uni))
  (= (mem (set1 (tuple21 int a)) r (seq a s))
  (and (<= 0 (size a r)) (mem (set1 (tuple21 int a)) r
  (seq_length a (size a r) s)))))))

;; seq_as_total_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (r uni))
  (=> (mem (set1 (tuple21 int a)) r (seq a s)) (mem (set1 (tuple21 int a)) r
  (infix_mnmngt a int (t2tb4 (mk 1 (size a r))) s))))))

(declare-fun seq1 (ty uni) uni)

;; seq1_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple21 int a))) (seq1 a x)))))

(declare-fun iseq (ty uni) uni)

;; iseq_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple21 int a))) (iseq a x)))))

(declare-fun iseq1 (ty uni) uni)

;; iseq1_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple21 int a))) (iseq1 a x)))))

(declare-fun perm (ty uni) uni)

;; perm_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple21 int a))) (perm a x)))))

(declare-fun is_finite_subset (ty uni uni Int) Bool)

;; Empty
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE))) (is_finite_subset
  enum_ETAT_AUTOMATE1 (t2tb empty1) (t2tb s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)) (c Int))
  (=> (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb (add1 x s1))
  (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)) (c Int))
  (=> (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset enum_ETAT_AUTOMATE1
  (t2tb (add1 x s1)) (t2tb s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2)
  (=> (not (mem a x s1)) (is_finite_subset a (add a x s1) s2 (+ c 1))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set enum_ETAT_AUTOMATE)) (z1 (set enum_ETAT_AUTOMATE))
  (z2 Int))
  (=> (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb z) (t2tb z1) z2)
  (or
  (or
  (exists ((s (set enum_ETAT_AUTOMATE)))
  (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)) (c Int))
  (and (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1) (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)) (c Int))
  (and (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2) c)
  (and (mem1 x s2)
  (and (not (mem1 x s1))
  (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 Int))
  (=> (sort (set1 a) z)
  (=> (sort (set1 a) z1)
  (=> (is_finite_subset a z z1 z2)
  (or
  (or
  (exists ((s uni))
  (and (sort (set1 a) s) (and (and (= z (empty a)) (= z1 s)) (= z2 0))))
  (exists ((x uni) (s1 uni) (s2 uni) (c Int))
  (and (sort a x)
  (and (sort (set1 a) s1)
  (and (sort (set1 a) s2)
  (and (is_finite_subset a s1 s2 c)
  (and (mem a x s2)
  (and (mem a x s1) (and (and (= z (add a x s1)) (= z1 s2)) (= z2 c))))))))))
  (exists ((x uni) (s1 uni) (s2 uni) (c Int))
  (and (sort a x)
  (and (sort (set1 a) s1)
  (and (sort (set1 a) s2)
  (and (is_finite_subset a s1 s2 c)
  (and (mem a x s2)
  (and (not (mem a x s1))
  (and (and (= z (add a x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))))))))

;; finite_interval
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b) (is_finite_subset int (t2tb4 (mk a b)) (t2tb4 integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb4 (mk a b)) (t2tb4 integer) 0))))

(declare-fun finite_subsets (ty uni) uni)

;; finite_subsets_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (finite_subsets a x)))))

;; finite_subsets_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE))) (mem (set1 enum_ETAT_AUTOMATE1)
  (t2tb empty1) (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)))
  (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))
  (=> (mem1 x s2) (mem (set1 enum_ETAT_AUTOMATE1) (t2tb (add1 x s1))
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE))
  (s3 (set enum_ETAT_AUTOMATE)))
  (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3)))
  (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s2)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3))) (mem
  (set1 enum_ETAT_AUTOMATE1) (t2tb (union1 s1 s2))
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3)))))))

;; finite_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

;; finite_inversion
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE)))
  (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))
  (or (= s1 empty1)
  (exists ((x enum_ETAT_AUTOMATE) (s3 (set enum_ETAT_AUTOMATE)))
  (and (= s1 (add1 x s3)) (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s3)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))))))))

;; finite_inversion
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni))
  (=> (sort (set1 a) s1)
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (or (= s1 (empty a))
  (exists ((x uni) (s3 uni))
  (and (sort a x)
  (and (sort (set1 a) s3)
  (and (= s1 (add a x s3)) (mem (set1 a) s3 (finite_subsets a s2))))))))))))

(declare-fun non_empty_finite_subsets (ty uni) uni)

;; non_empty_finite_subsets_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (non_empty_finite_subsets a x)))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE)) (x (set enum_ETAT_AUTOMATE)))
  (= (mem (set1 enum_ETAT_AUTOMATE1) (t2tb x)
  (non_empty_finite_subsets enum_ETAT_AUTOMATE1 (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset enum_ETAT_AUTOMATE1 (t2tb x) (t2tb s) c)
  (not (= x empty1)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (=> (sort (set1 a) x)
  (= (mem (set1 a) x (non_empty_finite_subsets a s))
  (exists ((c Int)) (and (is_finite_subset a x s c) (not (= x (empty a))))))))))

;; card_non_neg
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (c Int)) (=> (is_finite_subset a x s c) (<= 0 c)))))

;; card_unique
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (c1 Int) (c2 Int))
  (=> (is_finite_subset a x s c1) (=> (is_finite_subset a x s c2) (= c1 c2))))))

(declare-fun card (ty uni) Int)

;; card_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (c Int))
  (=> (is_finite_subset a x s c) (= (card a x) c)))))

;; card_Empty
  (assert (= (card enum_ETAT_AUTOMATE1 (t2tb empty1)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)))
  (! (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
     (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))
     (=> (not (mem1 x s1))
     (= (card enum_ETAT_AUTOMATE1 (t2tb (add1 x s1))) (+ (card
                                                         enum_ETAT_AUTOMATE1
                                                         (t2tb s1)) 1)))) :pattern ((mem
  (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))
  (card enum_ETAT_AUTOMATE1 (t2tb (add1 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x enum_ETAT_AUTOMATE) (s1 (set enum_ETAT_AUTOMATE))
  (s2 (set enum_ETAT_AUTOMATE)))
  (! (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
     (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))
     (=> (mem1 x s1)
     (= (card enum_ETAT_AUTOMATE1 (t2tb (add1 x s1))) (card
                                                      enum_ETAT_AUTOMATE1
                                                      (t2tb s1))))) :pattern ((mem
  (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s2)))
  (card enum_ETAT_AUTOMATE1 (t2tb (add1 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (mem a x s1) (= (card a (add a x s1)) (card a s1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Union
  (assert
  (forall ((s1 (set enum_ETAT_AUTOMATE)) (s2 (set enum_ETAT_AUTOMATE))
  (s3 (set enum_ETAT_AUTOMATE)))
  (! (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
     (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3)))
     (=> (mem (set1 enum_ETAT_AUTOMATE1) (t2tb s2)
     (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3)))
     (=> (is_empty enum_ETAT_AUTOMATE1
     (inter enum_ETAT_AUTOMATE1 (t2tb s1) (t2tb s2)))
     (= (card enum_ETAT_AUTOMATE1 (t2tb (union1 s1 s2))) (+ (card
                                                            enum_ETAT_AUTOMATE1
                                                            (t2tb s1)) 
     (card enum_ETAT_AUTOMATE1 (t2tb s2))))))) :pattern ((mem
  (set1 enum_ETAT_AUTOMATE1) (t2tb s1)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3))) (mem
  (set1 enum_ETAT_AUTOMATE1) (t2tb s2)
  (finite_subsets enum_ETAT_AUTOMATE1 (t2tb s3)))
  (card enum_ETAT_AUTOMATE1 (t2tb (union1 s1 s2)))) )))

;; card_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s3))
     (=> (mem (set1 a) s2 (finite_subsets a s3))
     (=> (is_empty a (inter a s1 s2))
     (= (card a (union a s1 s2)) (+ (card a s1) (card a s2)))))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s3)) (mem (set1 a) s2 (finite_subsets a s3))
  (card a (union a s1 s2))) ))))

(declare-fun times (ty ty uni uni) uni)

;; times_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b)) (times b a x x1)))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set enum_ETAT_AUTOMATE)) (x uni)
  (y enum_ETAT_AUTOMATE))
  (! (= (mem (tuple21 a enum_ETAT_AUTOMATE1)
     (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y))
     (times enum_ETAT_AUTOMATE1 a a1 (t2tb b)))
     (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a enum_ETAT_AUTOMATE1) (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y))
  (times enum_ETAT_AUTOMATE1 a a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a (set enum_ETAT_AUTOMATE)) (b (set enum_ETAT_AUTOMATE))
  (x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (! (= (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
     (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
     (times enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb a) (t2tb b)))
     (and (mem1 x a) (mem1 y b))) :pattern ((mem
  (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (times enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set enum_ETAT_AUTOMATE)) (b1 uni) (x enum_ETAT_AUTOMATE)
  (y uni))
  (! (= (mem (tuple21 enum_ETAT_AUTOMATE1 b)
     (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
     (times b enum_ETAT_AUTOMATE1 (t2tb a) b1))
     (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 enum_ETAT_AUTOMATE1 b) (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
  (times b enum_ETAT_AUTOMATE1 (t2tb a) b1))) ))))

;; times_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((a1 uni) (b1 uni) (x uni) (y uni))
  (! (= (mem (tuple21 a b) (Tuple2 a b x y) (times b a a1 b1))
     (and (mem a x a1) (mem b y b1))) :pattern ((mem
  (tuple21 a b) (Tuple2 a b x y) (times b a a1 b1))) ))))

(declare-fun relations (ty ty uni uni) uni)

;; relations_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (relations b a x x1)))))

;; relations_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((u uni) (v uni))
  (= (relations b a u v) (power (tuple21 a b) (times b a u v))))))

;; break_mem_in_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((c uni) (s uni) (x uni) (y uni))
  (=> (sort (tuple21 a b) c)
  (= (mem (tuple21 a b) c (add (tuple21 a b) (Tuple2 a b x y) s))
  (or (= c (Tuple2 a b x y)) (mem (tuple21 a b) c s)))))))

;; break_power_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (= (mem (set1 (tuple21 a b)) r (power (tuple21 a b) (times b a u v)))
  (subset (tuple21 a b) r (times b a u v))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set enum_ETAT_AUTOMATE)))
  (and
  (=> (subset (tuple21 a enum_ETAT_AUTOMATE1) r
  (times enum_ETAT_AUTOMATE1 a u (t2tb v)))
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) r) (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y enum_ETAT_AUTOMATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_ETAT_AUTOMATE1)
  (Tuple2 a enum_ETAT_AUTOMATE1 x (t2tb1 y)) r) (and (mem a x u) (mem1 y v)))))
  (subset (tuple21 a enum_ETAT_AUTOMATE1) r
  (times enum_ETAT_AUTOMATE1 a u (t2tb v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE)))
  (u (set enum_ETAT_AUTOMATE)) (v (set enum_ETAT_AUTOMATE)))
  (= (subset (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1) (t2tb8 r)
  (times enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb u) (t2tb v)))
  (forall ((x enum_ETAT_AUTOMATE) (y enum_ETAT_AUTOMATE))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1)
  (Tuple2 enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb1 x) (t2tb1 y))
  (t2tb8 r)) (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set enum_ETAT_AUTOMATE)) (v uni))
  (and
  (=> (subset (tuple21 enum_ETAT_AUTOMATE1 b) r
  (times b enum_ETAT_AUTOMATE1 (t2tb u) v))
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) r) (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x enum_ETAT_AUTOMATE) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) r) (and (mem1 x u) (mem b y v)))))
  (subset (tuple21 enum_ETAT_AUTOMATE1 b) r
  (times b enum_ETAT_AUTOMATE1 (t2tb u) v)))))))

;; subset_of_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (and
  (=> (subset (tuple21 a b) r (times b a u v))
  (forall ((x uni) (y uni))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) r) (and (mem a x u) (mem b y v)))))
  (=>
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y)
  (=> (mem (tuple21 a b) (Tuple2 a b x y) r) (and (mem a x u) (mem b y v))))))
  (subset (tuple21 a b) r (times b a u v)))))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y enum_ETAT_AUTOMATE))
  (! (=> (mem a x s)
     (= (tb2t1
        (apply enum_ETAT_AUTOMATE1 a
        (times enum_ETAT_AUTOMATE1 a s (t2tb (add1 y empty1))) x)) y)) :pattern (
  (tb2t1
  (apply enum_ETAT_AUTOMATE1 a
  (times enum_ETAT_AUTOMATE1 a s (t2tb (add1 y empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((s (set enum_ETAT_AUTOMATE)) (x enum_ETAT_AUTOMATE)
  (y enum_ETAT_AUTOMATE))
  (! (=> (mem1 x s)
     (= (tb2t1
        (apply enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1
        (times enum_ETAT_AUTOMATE1 enum_ETAT_AUTOMATE1 (t2tb s)
        (t2tb (add1 y empty1))) (t2tb1 x))) y)) :pattern ((tb2t1
                                                          (apply
                                                          enum_ETAT_AUTOMATE1
                                                          enum_ETAT_AUTOMATE1
                                                          (times
                                                          enum_ETAT_AUTOMATE1
                                                          enum_ETAT_AUTOMATE1
                                                          (t2tb s)
                                                          (t2tb
                                                          (add1 y empty1)))
                                                          (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set enum_ETAT_AUTOMATE)) (x enum_ETAT_AUTOMATE) (y uni))
  (! (=> (sort b y)
     (=> (mem1 x s)
     (= (apply b enum_ETAT_AUTOMATE1
        (times b enum_ETAT_AUTOMATE1 (t2tb s) (add b y (empty b))) (t2tb1 x)) y))) :pattern (
  (apply b enum_ETAT_AUTOMATE1
  (times b enum_ETAT_AUTOMATE1 (t2tb s) (add b y (empty b))) (t2tb1 x))) ))))

;; apply_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (x uni) (y uni))
  (! (=> (sort b y)
     (=> (mem a x s) (= (apply b a (times b a s (add b y (empty b))) x) y))) :pattern (
  (apply b a (times b a s (add b y (empty b))) x)) ))))

(declare-fun infix_lspl (ty ty uni uni) uni)

;; infix <+_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (infix_lspl b a x x1)))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x enum_ETAT_AUTOMATE) (y uni) (q uni) (r uni))
  (= (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
  (infix_lspl b enum_ETAT_AUTOMATE1 q r))
  (ite (mem1 x (tb2t (dom b enum_ETAT_AUTOMATE1 r))) (mem
  (tuple21 enum_ETAT_AUTOMATE1 b) (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y)
  r) (mem (tuple21 enum_ETAT_AUTOMATE1 b)
  (Tuple2 enum_ETAT_AUTOMATE1 b (t2tb1 x) y) q))))))

;; overriding_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni) (q uni) (r uni))
  (= (mem (tuple21 a b) (Tuple2 a b x y) (infix_lspl b a q r))
  (ite (mem a x (dom b a r)) (mem (tuple21 a b) (Tuple2 a b x y) r) (mem
  (tuple21 a b) (Tuple2 a b x y) q))))))

;; function_overriding
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (f uni) (g uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple21 a b)) g (infix_plmngt b a s t))) (mem (set1 (tuple21 a b))
  (infix_lspl b a f g) (infix_plmngt b a s t))))))

;; dom_overriding
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni))
  (! (= (tb2t
        (dom b enum_ETAT_AUTOMATE1 (infix_lspl b enum_ETAT_AUTOMATE1 f g))) 
  (union1 (tb2t (dom b enum_ETAT_AUTOMATE1 f))
  (tb2t (dom b enum_ETAT_AUTOMATE1 g)))) :pattern ((tb2t
                                                   (dom b enum_ETAT_AUTOMATE1
                                                   (infix_lspl b
                                                   enum_ETAT_AUTOMATE1 f g)))) ))))

;; dom_overriding
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (g uni))
  (! (= (dom b a (infix_lspl b a f g)) (union a (dom b a f) (dom b a g))) :pattern (
  (dom b a (infix_lspl b a f g))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set enum_ETAT_AUTOMATE)) (t uni) (f uni) (g uni)
  (x enum_ETAT_AUTOMATE))
  (! (=>
     (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
     (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)) (mem
     (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) g
     (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)))
     (=> (mem1 x (tb2t (dom b enum_ETAT_AUTOMATE1 g)))
     (= (apply b enum_ETAT_AUTOMATE1 (infix_lspl b enum_ETAT_AUTOMATE1 f g)
        (t2tb1 x)) (apply b enum_ETAT_AUTOMATE1 g (t2tb1 x))))) :pattern ((mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)) (mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) g
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (apply b enum_ETAT_AUTOMATE1 (infix_lspl b enum_ETAT_AUTOMATE1 f g)
  (t2tb1 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (f uni) (g uni) (x uni))
  (! (=>
     (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
     (set1 (tuple21 a b)) g (infix_plmngt b a s t)))
     (=> (mem a x (dom b a g))
     (= (apply b a (infix_lspl b a f g) x) (apply b a g x)))) :pattern ((mem
  (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem (set1 (tuple21 a b)) g
  (infix_plmngt b a s t)) (apply b a (infix_lspl b a f g) x)) ))))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set enum_ETAT_AUTOMATE)) (t uni) (f uni) (g uni)
  (x enum_ETAT_AUTOMATE))
  (! (=>
     (and (mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
     (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)) (mem
     (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) g
     (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t)))
     (=> (not (mem1 x (tb2t (dom b enum_ETAT_AUTOMATE1 g))))
     (=> (mem1 x (tb2t (dom b enum_ETAT_AUTOMATE1 f)))
     (= (apply b enum_ETAT_AUTOMATE1 (infix_lspl b enum_ETAT_AUTOMATE1 f g)
        (t2tb1 x)) (apply b enum_ETAT_AUTOMATE1 f (t2tb1 x)))))) :pattern ((mem
  (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) f
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (apply b enum_ETAT_AUTOMATE1 (infix_lspl b enum_ETAT_AUTOMATE1 f g)
  (t2tb1 x))) :pattern ((mem (set1 (tuple21 enum_ETAT_AUTOMATE1 b)) g
  (infix_plmngt b enum_ETAT_AUTOMATE1 (t2tb s) t))
  (apply b enum_ETAT_AUTOMATE1 (infix_lspl b enum_ETAT_AUTOMATE1 f g)
  (t2tb1 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (f uni) (g uni) (x uni))
  (! (=>
     (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
     (set1 (tuple21 a b)) g (infix_plmngt b a s t)))
     (=> (not (mem a x (dom b a g)))
     (=> (mem a x (dom b a f))
     (= (apply b a (infix_lspl b a f g) x) (apply b a f x))))) :pattern ((mem
  (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (apply b a (infix_lspl b a f g) x)) :pattern ((mem (set1 (tuple21 a b)) g
  (infix_plmngt b a s t)) (apply b a (infix_lspl b a f g) x)) ))))

(declare-fun uninterpreted_type () ty)

(declare-fun E_Traitement_carte () enum_ETAT_AUTOMATE)

(declare-fun E_Traitement_code () enum_ETAT_AUTOMATE)

(declare-fun E_Traitement_somme () enum_ETAT_AUTOMATE)

(declare-fun E_Distribution_billets () enum_ETAT_AUTOMATE)

(declare-fun E_Restitution_carte () enum_ETAT_AUTOMATE)

(declare-fun E_Confiscation_carte () enum_ETAT_AUTOMATE)

(declare-fun E_Veille () enum_ETAT_AUTOMATE)

(declare-fun match_enum_ETAT_AUTOMATE (ty enum_ETAT_AUTOMATE uni uni uni uni
  uni uni uni) uni)

;; match_enum_ETAT_AUTOMATE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_ETAT_AUTOMATE) (x1 uni) (x2 uni) (x3 uni) (x4 uni)
  (x5 uni) (x6 uni) (x7 uni)) (sort a
  (match_enum_ETAT_AUTOMATE a x x1 x2 x3 x4 x5 x6 x7)))))

;; match_enum_ETAT_AUTOMATE_E_Traitement_carte
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z)
  (= (match_enum_ETAT_AUTOMATE a E_Traitement_carte z z1 z2 z3 z4 z5 z6) z)))))

;; match_enum_ETAT_AUTOMATE_E_Traitement_code
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z1)
  (= (match_enum_ETAT_AUTOMATE a E_Traitement_code z z1 z2 z3 z4 z5 z6) z1)))))

;; match_enum_ETAT_AUTOMATE_E_Traitement_somme
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z2)
  (= (match_enum_ETAT_AUTOMATE a E_Traitement_somme z z1 z2 z3 z4 z5 z6) z2)))))

;; match_enum_ETAT_AUTOMATE_E_Distribution_billets
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z3)
  (= (match_enum_ETAT_AUTOMATE a E_Distribution_billets z z1 z2 z3 z4 z5 z6) z3)))))

;; match_enum_ETAT_AUTOMATE_E_Restitution_carte
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z4)
  (= (match_enum_ETAT_AUTOMATE a E_Restitution_carte z z1 z2 z3 z4 z5 z6) z4)))))

;; match_enum_ETAT_AUTOMATE_E_Confiscation_carte
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z5)
  (= (match_enum_ETAT_AUTOMATE a E_Confiscation_carte z z1 z2 z3 z4 z5 z6) z5)))))

;; match_enum_ETAT_AUTOMATE_E_Veille
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z6)
  (= (match_enum_ETAT_AUTOMATE a E_Veille z z1 z2 z3 z4 z5 z6) z6)))))

(declare-fun index_enum_ETAT_AUTOMATE (enum_ETAT_AUTOMATE) Int)

;; index_enum_ETAT_AUTOMATE_E_Traitement_carte
  (assert (= (index_enum_ETAT_AUTOMATE E_Traitement_carte) 0))

;; index_enum_ETAT_AUTOMATE_E_Traitement_code
  (assert (= (index_enum_ETAT_AUTOMATE E_Traitement_code) 1))

;; index_enum_ETAT_AUTOMATE_E_Traitement_somme
  (assert (= (index_enum_ETAT_AUTOMATE E_Traitement_somme) 2))

;; index_enum_ETAT_AUTOMATE_E_Distribution_billets
  (assert (= (index_enum_ETAT_AUTOMATE E_Distribution_billets) 3))

;; index_enum_ETAT_AUTOMATE_E_Restitution_carte
  (assert (= (index_enum_ETAT_AUTOMATE E_Restitution_carte) 4))

;; index_enum_ETAT_AUTOMATE_E_Confiscation_carte
  (assert (= (index_enum_ETAT_AUTOMATE E_Confiscation_carte) 5))

;; index_enum_ETAT_AUTOMATE_E_Veille
  (assert (= (index_enum_ETAT_AUTOMATE E_Veille) 6))

;; enum_ETAT_AUTOMATE_inversion
  (assert
  (forall ((u enum_ETAT_AUTOMATE))
  (or
  (or
  (or
  (or
  (or (or (= u E_Traitement_carte) (= u E_Traitement_code))
  (= u E_Traitement_somme)) (= u E_Distribution_billets))
  (= u E_Restitution_carte)) (= u E_Confiscation_carte)) (= u E_Veille))))

(declare-fun set_enum_ETAT_AUTOMATE () (set enum_ETAT_AUTOMATE))

;; set_enum_ETAT_AUTOMATE_axiom
  (assert (forall ((x enum_ETAT_AUTOMATE)) (mem1 x set_enum_ETAT_AUTOMATE)))

(declare-sort enum_ETAT_DAB 0)

(declare-fun enum_ETAT_DAB1 () ty)

(declare-fun E_Hors_service () enum_ETAT_DAB)

(declare-fun E_En_service () enum_ETAT_DAB)

(declare-fun match_enum_ETAT_DAB (ty enum_ETAT_DAB uni uni) uni)

;; match_enum_ETAT_DAB_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_ETAT_DAB) (x1 uni) (x2 uni)) (sort a
  (match_enum_ETAT_DAB a x x1 x2)))))

;; match_enum_ETAT_DAB_E_Hors_service
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_ETAT_DAB a E_Hors_service z z1) z)))))

;; match_enum_ETAT_DAB_E_En_service
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_ETAT_DAB a E_En_service z z1) z1)))))

(declare-fun index_enum_ETAT_DAB (enum_ETAT_DAB) Int)

;; index_enum_ETAT_DAB_E_Hors_service
  (assert (= (index_enum_ETAT_DAB E_Hors_service) 0))

;; index_enum_ETAT_DAB_E_En_service
  (assert (= (index_enum_ETAT_DAB E_En_service) 1))

;; enum_ETAT_DAB_inversion
  (assert
  (forall ((u enum_ETAT_DAB)) (or (= u E_Hors_service) (= u E_En_service))))

(declare-fun set_enum_ETAT_DAB () (set enum_ETAT_DAB))

(declare-fun t2tb10 ((set enum_ETAT_DAB)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_ETAT_DAB))) (sort (set1 enum_ETAT_DAB1) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set enum_ETAT_DAB))

;; BridgeL
  (assert
  (forall ((i (set enum_ETAT_DAB)))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_ETAT_DAB1) j) (= (t2tb10 (tb2t10 j)) j)) :pattern (
  (t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 (enum_ETAT_DAB) uni)

;; t2tb_sort
  (assert (forall ((x enum_ETAT_DAB)) (sort enum_ETAT_DAB1 (t2tb11 x))))

(declare-fun tb2t11 (uni) enum_ETAT_DAB)

;; BridgeL
  (assert
  (forall ((i enum_ETAT_DAB))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_ETAT_DAB1 j) (= (t2tb11 (tb2t11 j)) j)) :pattern (
  (t2tb11 (tb2t11 j))) )))

;; set_enum_ETAT_DAB_axiom
  (assert
  (forall ((x enum_ETAT_DAB)) (mem enum_ETAT_DAB1 (t2tb11 x)
  (t2tb10 set_enum_ETAT_DAB))))

(declare-sort enum_STATUT 0)

(declare-fun enum_STATUT1 () ty)

(declare-fun E_Valide () enum_STATUT)

(declare-fun E_Invalide () enum_STATUT)

(declare-fun E_Illisible () enum_STATUT)

(declare-fun E_Interdite () enum_STATUT)

(declare-fun E_Perimee () enum_STATUT)

(declare-fun E_Epuisee () enum_STATUT)

(declare-fun E_Nouvel () enum_STATUT)

(declare-fun E_Dernier () enum_STATUT)

(declare-fun E_Hors_delai () enum_STATUT)

(declare-fun E_Incident () enum_STATUT)

(declare-fun match_enum_STATUT (ty enum_STATUT uni uni uni uni uni uni uni
  uni uni uni) uni)

;; match_enum_STATUT_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_STATUT) (x1 uni) (x2 uni) (x3 uni) (x4 uni) (x5 uni)
  (x6 uni) (x7 uni) (x8 uni) (x9 uni) (x10 uni)) (sort a
  (match_enum_STATUT a x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)))))

;; match_enum_STATUT_E_Valide
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z)
  (= (match_enum_STATUT a E_Valide z z1 z2 z3 z4 z5 z6 z7 z8 z9) z)))))

;; match_enum_STATUT_E_Invalide
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z1)
  (= (match_enum_STATUT a E_Invalide z z1 z2 z3 z4 z5 z6 z7 z8 z9) z1)))))

;; match_enum_STATUT_E_Illisible
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z2)
  (= (match_enum_STATUT a E_Illisible z z1 z2 z3 z4 z5 z6 z7 z8 z9) z2)))))

;; match_enum_STATUT_E_Interdite
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z3)
  (= (match_enum_STATUT a E_Interdite z z1 z2 z3 z4 z5 z6 z7 z8 z9) z3)))))

;; match_enum_STATUT_E_Perimee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z4)
  (= (match_enum_STATUT a E_Perimee z z1 z2 z3 z4 z5 z6 z7 z8 z9) z4)))))

;; match_enum_STATUT_E_Epuisee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z5)
  (= (match_enum_STATUT a E_Epuisee z z1 z2 z3 z4 z5 z6 z7 z8 z9) z5)))))

;; match_enum_STATUT_E_Nouvel
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z6)
  (= (match_enum_STATUT a E_Nouvel z z1 z2 z3 z4 z5 z6 z7 z8 z9) z6)))))

;; match_enum_STATUT_E_Dernier
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z7)
  (= (match_enum_STATUT a E_Dernier z z1 z2 z3 z4 z5 z6 z7 z8 z9) z7)))))

;; match_enum_STATUT_E_Hors_delai
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z8)
  (= (match_enum_STATUT a E_Hors_delai z z1 z2 z3 z4 z5 z6 z7 z8 z9) z8)))))

;; match_enum_STATUT_E_Incident
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z9)
  (= (match_enum_STATUT a E_Incident z z1 z2 z3 z4 z5 z6 z7 z8 z9) z9)))))

(declare-fun index_enum_STATUT (enum_STATUT) Int)

;; index_enum_STATUT_E_Valide
  (assert (= (index_enum_STATUT E_Valide) 0))

;; index_enum_STATUT_E_Invalide
  (assert (= (index_enum_STATUT E_Invalide) 1))

;; index_enum_STATUT_E_Illisible
  (assert (= (index_enum_STATUT E_Illisible) 2))

;; index_enum_STATUT_E_Interdite
  (assert (= (index_enum_STATUT E_Interdite) 3))

;; index_enum_STATUT_E_Perimee
  (assert (= (index_enum_STATUT E_Perimee) 4))

;; index_enum_STATUT_E_Epuisee
  (assert (= (index_enum_STATUT E_Epuisee) 5))

;; index_enum_STATUT_E_Nouvel
  (assert (= (index_enum_STATUT E_Nouvel) 6))

;; index_enum_STATUT_E_Dernier
  (assert (= (index_enum_STATUT E_Dernier) 7))

;; index_enum_STATUT_E_Hors_delai
  (assert (= (index_enum_STATUT E_Hors_delai) 8))

;; index_enum_STATUT_E_Incident
  (assert (= (index_enum_STATUT E_Incident) 9))

;; enum_STATUT_inversion
  (assert
  (forall ((u enum_STATUT))
  (or
  (or
  (or
  (or
  (or
  (or
  (or (or (or (= u E_Valide) (= u E_Invalide)) (= u E_Illisible))
  (= u E_Interdite)) (= u E_Perimee)) (= u E_Epuisee)) (= u E_Nouvel))
  (= u E_Dernier)) (= u E_Hors_delai)) (= u E_Incident))))

(declare-fun set_enum_STATUT () (set enum_STATUT))

(declare-fun t2tb12 ((set enum_STATUT)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_STATUT))) (sort (set1 enum_STATUT1) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set enum_STATUT))

;; BridgeL
  (assert
  (forall ((i (set enum_STATUT)))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_STATUT1) j) (= (t2tb12 (tb2t12 j)) j)) :pattern (
  (t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 (enum_STATUT) uni)

;; t2tb_sort
  (assert (forall ((x enum_STATUT)) (sort enum_STATUT1 (t2tb13 x))))

(declare-fun tb2t13 (uni) enum_STATUT)

;; BridgeL
  (assert
  (forall ((i enum_STATUT))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_STATUT1 j) (= (t2tb13 (tb2t13 j)) j)) :pattern ((t2tb13
                                                                    (tb2t13
                                                                    j))) )))

;; set_enum_STATUT_axiom
  (assert
  (forall ((x enum_STATUT)) (mem enum_STATUT1 (t2tb13 x)
  (t2tb12 set_enum_STATUT))))

(declare-fun f1 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f1_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool)) (f1 v_tst_dab v_rslt
  v_resultat v_precedent v_panne_dab v_etat_dab v_etat v_cse_vde v_courant
  v_caisse_vde)))

(declare-fun f2 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f2_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f2 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service)))))

(declare-fun f6 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f6_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f6 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (= E_Veille E_Traitement_carte)))))

(declare-fun f8 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f8_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f8 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service)))))

(declare-fun f11 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f11_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f11 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Traitement_carte)))))

(declare-fun f13 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f13_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f13 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Traitement_code)))))

(declare-fun f15 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f15_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f15 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Traitement_somme)))))

(declare-fun f17 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f17_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f17 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Distribution_billets)))))

(declare-fun f19 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f19_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f19 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service)))))

(declare-fun f22 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f22_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f22 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Traitement_carte)))))

(declare-fun f24 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f24_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f24 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Traitement_code)))))

(declare-fun f26 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f26_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f26 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (= E_Veille E_Restitution_carte)))))

(declare-fun f28 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f28_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f28 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (=> (or (= v_panne_dab true) (= v_caisse_vde true))
  (= v_etat_dab E_Hors_service))
  (=> (= v_etat_dab E_Hors_service)
  (or (= v_panne_dab true) (= v_caisse_vde true))))
  (=> (and (= v_courant E_Traitement_code) (= v_etat_dab E_En_service))
  (and
  (and (mem1 v_precedent
  (union1 (add1 E_Traitement_code empty1) (add1 E_Traitement_carte empty1)))
  (=> (= v_precedent E_Traitement_code) (mem enum_STATUT1 (t2tb13 v_resultat)
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Nouvel) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Dernier) (empty enum_STATUT1))))))
  (=> (= v_precedent E_Traitement_carte) (= v_resultat E_Valide)))))
  (=> (and (= v_courant E_Restitution_carte) (= v_etat_dab E_En_service))
  (and
  (and
  (and
  (and (mem1 v_precedent
  (union1
  (union1
  (union1 (add1 E_Traitement_carte empty1) (add1 E_Traitement_code empty1))
  (add1 E_Traitement_somme empty1)) (add1 E_Distribution_billets empty1)))
  (=> (= v_precedent E_Traitement_carte) (mem enum_STATUT1
  (t2tb13 v_resultat)
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Perimee) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Epuisee) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Illisible) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Invalide) (empty enum_STATUT1))))))
  (=> (= v_precedent E_Traitement_code) (mem enum_STATUT1 (t2tb13 v_resultat)
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))))))
  (=> (= v_precedent E_Traitement_somme) (mem enum_STATUT1
  (t2tb13 v_resultat)
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Invalide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))))))
  (=> (= v_precedent E_Distribution_billets) (mem enum_STATUT1
  (t2tb13 v_resultat)
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Valide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))))))))
  (=> (and (= v_courant E_Confiscation_carte) (= v_etat_dab E_En_service))
  (and
  (and
  (and (mem1 v_precedent
  (union1
  (union1 (add1 E_Traitement_carte empty1) (add1 E_Traitement_code empty1))
  (add1 E_Restitution_carte empty1)))
  (=> (= v_precedent E_Traitement_carte) (= v_resultat E_Interdite)))
  (=> (= v_precedent E_Traitement_code) (= v_resultat E_Invalide)))
  (=> (= v_precedent E_Restitution_carte) (mem enum_STATUT1
  (t2tb13 v_resultat)
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1)))))))))))

(declare-fun f29 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f29_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f29 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde) (= E_En_service E_Hors_service))))

(declare-fun f32 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f32_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f32 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde) (= E_Veille E_Traitement_code))))

(declare-fun f35 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f35_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f35 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Traitement_code) (= E_Veille E_Traitement_carte)))))

(declare-fun f37 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f37_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f37 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde) (= E_Veille E_Restitution_carte))))

(declare-fun f39 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f39_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f39 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Restitution_carte) (= E_Veille E_Traitement_carte)))))

(declare-fun f41 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f41_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f41 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Restitution_carte) (= E_Veille E_Traitement_code)))))

(declare-fun f43 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f43_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f43 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Restitution_carte) (= E_Veille E_Traitement_somme)))))

(declare-fun f45 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f45_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f45 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Restitution_carte) (= E_Veille E_Distribution_billets)))))

(declare-fun f47 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f47_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f47 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde) (= E_Veille E_Confiscation_carte))))

(declare-fun f49 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f49_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f49 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Confiscation_carte) (= E_Veille E_Traitement_carte)))))

(declare-fun f51 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f51_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f51 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Confiscation_carte) (= E_Veille E_Traitement_code)))))

(declare-fun f53 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f53_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f53 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Confiscation_carte) (= E_Veille E_Restitution_carte)))))

(declare-fun f55 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f55_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f55 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (or (= v_tst_dab true) (= v_cse_vde true)))))

(declare-fun f56 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f56_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f56 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= v_courant E_Traitement_code) (= E_Hors_service E_En_service)))))

(declare-fun f58 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f58_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f58 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= v_courant E_Traitement_code) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_code)))))

(declare-fun f60 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f60_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f60 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= v_courant E_Traitement_code) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_carte)))))

(declare-fun f62 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f62_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f62 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= v_courant E_Restitution_carte) (= E_Hors_service E_En_service)))))

(declare-fun f64 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f64_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f64 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Restitution_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_carte)))))

(declare-fun f66 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f66_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f66 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Restitution_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_code)))))

(declare-fun f68 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f68_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f68 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Restitution_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_somme)))))

(declare-fun f70 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f70_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f70 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Restitution_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Distribution_billets)))))

(declare-fun f72 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f72_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f72 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= v_courant E_Confiscation_carte) (= E_Hors_service E_En_service)))))

(declare-fun f74 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f74_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f74 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Confiscation_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_carte)))))

(declare-fun f76 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f76_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f76 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Confiscation_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Traitement_code)))))

(declare-fun f78 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f78_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f78 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and (= v_courant E_Confiscation_carte) (= E_Hors_service E_En_service))
  (= v_precedent E_Restitution_carte)))))

(declare-fun f80 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f80_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f80 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde) (= v_etat_dab E_Hors_service))))

(declare-fun f81 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f81_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f81 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Traitement_code) (= v_etat_dab E_En_service)))))

(declare-fun f83 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f83_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f83 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Traitement_code) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_code)))))

(declare-fun f84 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f84_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f84 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Traitement_code) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_carte)))))

(declare-fun f85 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f85_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f85 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Restitution_carte) (= v_etat_dab E_En_service)))))

(declare-fun f87 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f87_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f87 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_carte)))))

(declare-fun f88 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f88_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f88 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_code)))))

(declare-fun f89 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f89_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f89 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_somme)))))

(declare-fun f90 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f90_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f90 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Restitution_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Distribution_billets)))))

(declare-fun f91 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f91_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f91 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (= E_Veille E_Confiscation_carte) (= v_etat_dab E_En_service)))))

(declare-fun f93 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f93_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f93 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Confiscation_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_carte)))))

(declare-fun f94 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f94_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f94 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Confiscation_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Traitement_code)))))

(declare-fun f95 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f95_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f95 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (and (= E_Veille E_Confiscation_carte) (= v_etat_dab E_En_service))
  (= v_courant E_Restitution_carte)))))

(declare-fun f96 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f96_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f96 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab E_En_service) (= v_panne_dab false))
  (= v_caisse_vde false))
  (=> (= v_courant E_Traitement_carte) (mem enum_STATUT1 (t2tb13 v_rslt)
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Valide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Invalide) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Illisible) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Perimee) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Interdite) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Epuisee) (empty enum_STATUT1))))))
  (=> (= v_courant E_Traitement_code) (mem enum_STATUT1 (t2tb13 v_rslt)
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Valide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Invalide) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Nouvel) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Dernier) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))))))
  (=> (= v_courant E_Traitement_somme) (mem enum_STATUT1 (t2tb13 v_rslt)
  (union enum_STATUT1
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Valide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Invalide) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))))))
  (=> (mem1 v_courant
  (union1
  (union1 (add1 E_Distribution_billets empty1)
  (add1 E_Restitution_carte empty1)) (add1 E_Veille empty1))) (mem
  enum_STATUT1 (t2tb13 v_rslt)
  (union enum_STATUT1
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Valide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Hors_delai) (empty enum_STATUT1)))
  (add enum_STATUT1 (t2tb13 E_Incident) (empty enum_STATUT1))))))
  (=> (= v_courant E_Confiscation_carte) (mem enum_STATUT1 (t2tb13 v_rslt)
  (union enum_STATUT1
  (add enum_STATUT1 (t2tb13 E_Valide) (empty enum_STATUT1))
  (add enum_STATUT1 (t2tb13 E_Invalide) (empty enum_STATUT1)))))))))

(declare-fun f97 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f97_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f97 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Traitement_code)))))

(declare-fun f98 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f98_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f98 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Traitement_code)) (= v_courant E_Traitement_code)))))

(declare-fun f100 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f100_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f100 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Traitement_code)) (= v_courant E_Traitement_carte)))))

(declare-fun f102 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f102_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f102 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Restitution_carte)))))

(declare-fun f103 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f103_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f103 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Restitution_carte)) (= v_courant E_Traitement_carte)))))

(declare-fun f105 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f105_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f105 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Restitution_carte)) (= v_courant E_Traitement_code)))))

(declare-fun f107 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f107_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f107 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Restitution_carte)) (= v_courant E_Traitement_somme)))))

(declare-fun f109 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f109_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f109 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Restitution_carte)) (= v_courant E_Distribution_billets)))))

(declare-fun f111 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f111_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f111 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Confiscation_carte)))))

(declare-fun f112 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f112_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f112 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Confiscation_carte)) (= v_courant E_Traitement_carte)))))

(declare-fun f114 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f114_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f114 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Confiscation_carte)) (= v_courant E_Traitement_code)))))

(declare-fun f116 (Bool enum_STATUT enum_STATUT enum_ETAT_AUTOMATE Bool
  enum_ETAT_DAB enum_ETAT_AUTOMATE Bool enum_ETAT_AUTOMATE Bool) Bool)

;; f116_def
  (assert
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (= (f116 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_courant E_Veille)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille))))
  (=> (= v_courant E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant E_Restitution_carte)
  (and
  (and (=> (= v_rslt E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant E_Confiscation_carte) (= v_etat E_Veille)))
  (= v_etat E_Confiscation_carte)) (= v_courant E_Restitution_carte)))))

(assert
;; initialiser_etat_5
 ;; File "POwhy_bpo2why/DAB/Controleur.why", line 1794, characters 7-25
  (not
  (forall ((v_tst_dab Bool) (v_rslt enum_STATUT) (v_resultat enum_STATUT)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab Bool)
  (v_etat_dab enum_ETAT_DAB) (v_etat enum_ETAT_AUTOMATE) (v_cse_vde Bool)
  (v_courant enum_ETAT_AUTOMATE) (v_caisse_vde Bool))
  (=>
  (and (f1 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde)
  (and (f28 v_tst_dab v_rslt v_resultat v_precedent v_panne_dab v_etat_dab
  v_etat v_cse_vde v_courant v_caisse_vde) (f37 v_tst_dab v_rslt v_resultat
  v_precedent v_panne_dab v_etat_dab v_etat v_cse_vde v_courant
  v_caisse_vde))) (mem1 E_Veille
  (union1
  (union1
  (union1 (add1 E_Traitement_carte empty1) (add1 E_Traitement_code empty1))
  (add1 E_Traitement_somme empty1)) (add1 E_Distribution_billets empty1)))))))
(check-sat)
