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

(declare-fun power (Int Int) Int)

;; Power_0
  (assert (forall ((x Int)) (= (power x 0) 1)))

;; Power_s
  (assert
  (forall ((x Int) (n Int))
  (=> (<= 0 n) (= (power x (+ n 1)) (* x (power x n))))))

;; Power_s_alt
  (assert
  (forall ((x Int) (n Int))
  (=> (< 0 n) (= (power x n) (* x (power x (- n 1)))))))

;; Power_1
  (assert (forall ((x Int)) (= (power x 1) x)))

;; Power_sum
  (assert
  (forall ((x Int) (n Int) (m Int))
  (=> (<= 0 n)
  (=> (<= 0 m) (= (power x (+ n m)) (* (power x n) (power x m)))))))

;; Power_mult
  (assert
  (forall ((x Int) (n Int) (m Int))
  (=> (<= 0 n) (=> (<= 0 m) (= (power x (* n m)) (power (power x n) m))))))

;; Power_mult2
  (assert
  (forall ((x Int) (y Int) (n Int))
  (=> (<= 0 n) (= (power (* x y) n) (* (power x n) (power y n))))))

;; Power_non_neg
  (assert
  (forall ((x Int) (y Int)) (=> (and (<= 0 x) (<= 0 y)) (<= 0 (power x y)))))

;; Power_monotonic
  (assert
  (forall ((x Int) (n Int) (m Int))
  (=> (and (< 0 x) (and (<= 0 n) (<= n m))) (<= (power x n) (power x m)))))

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

(declare-fun mem (ty uni uni) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

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

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun empty (ty) uni)

;; empty_sort
  (assert (forall ((a ty)) (sort (set1 a) (empty a))))

(declare-fun empty1 () (set Bool))

(declare-fun empty2 () (set Int))

(declare-fun empty3 () (set (tuple2 Int Int)))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

(declare-fun t2tb5 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb5 x))))

(declare-fun tb2t5 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb5 (tb2t5 j)) j) :pattern ((t2tb5 (tb2t5 j))) )))

;; empty_def1
  (assert (is_empty (tuple21 int int) (t2tb5 empty3)))

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

;; empty_def1
  (assert (is_empty bool (t2tb3 empty1)))

(declare-fun t2tb ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb x))))

(declare-fun tb2t (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int))) (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni)) (! (= (t2tb (tb2t j)) j) :pattern ((t2tb (tb2t j))) )))

;; empty_def1
  (assert (is_empty int (t2tb empty2)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

(declare-fun t2tb6 ((tuple2 Int Int)) uni)

;; t2tb_sort
  (assert (forall ((x (tuple2 Int Int))) (sort (tuple21 int int) (t2tb6 x))))

(declare-fun tb2t6 (uni) (tuple2 Int Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Int)))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb6 (tb2t6 j)) j) :pattern ((t2tb6 (tb2t6 j))) )))

;; mem_empty
  (assert
  (forall ((x (tuple2 Int Int)))
  (not (mem (tuple21 int int) (t2tb6 x) (t2tb5 empty3)))))

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

;; mem_empty
  (assert (forall ((x Bool)) (not (mem bool (t2tb2 x) (t2tb3 empty1)))))

(declare-fun t2tb1 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb1 x))))

(declare-fun tb2t1 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb1 (tb2t1 j)) j) :pattern ((t2tb1 (tb2t1 j))) )))

;; mem_empty
  (assert (forall ((x Int)) (not (mem int (t2tb1 x) (t2tb empty2)))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (Int (set Int)) (set Int))

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int)))
  (= (mem int (t2tb1 x) (t2tb (add1 y s)))
  (or (= x y) (mem int (t2tb1 x) (t2tb s)))))))

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

;; remove_def1
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni) (s uni))
  (=> (sort a x)
  (=> (sort a y)
  (= (mem a x (remove a y s)) (and (not (= x y)) (mem a x s))))))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem int (t2tb1 x) (t2tb s))
  (= (add1 x (tb2t (remove int (t2tb1 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x Int) (s (set Int)))
  (= (tb2t (remove int (t2tb1 x) (t2tb (add1 x s)))) (tb2t
                                                     (remove int (t2tb1 x)
                                                     (t2tb s))))))

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
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (x uni))
  (= (mem a x (inter a s1 s2)) (and (mem a x s1) (mem a x s2))))))

(declare-fun diff (ty uni uni) uni)

;; diff_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (diff a x x1)))))

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
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb2 x) (t2tb3 b_bool))))

(declare-fun integer () (set Int))

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb1 x) (t2tb integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert (forall ((x Int)) (= (mem int (t2tb1 x) (t2tb natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert (forall ((x Int)) (= (mem int (t2tb1 x) (t2tb natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb1 x) (t2tb nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb1 x) (t2tb nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb1 x) (t2tb bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb1 x) (t2tb (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb1 x) (t2tb (mk a b)))) )))

;; interval_empty
  (assert (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) empty2))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b) (= (mk a b) (add1 b (mk a (- b 1)))))))

(declare-fun power1 (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power1 a x)))))

;; mem_power
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni))
  (! (= (mem (set1 a) x (power1 a y)) (subset a x y)) :pattern ((mem 
  (set1 a) x (power1 a y))) ))))

(declare-fun non_empty_power (ty uni) uni)

;; non_empty_power_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (non_empty_power a x)))))

(declare-fun t2tb4 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb4 (tb2t4 j)) j) :pattern ((t2tb4 (tb2t4 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (! (= (mem (set1 (tuple21 int int)) (t2tb5 x)
     (non_empty_power (tuple21 int int) (t2tb5 y)))
     (and (subset (tuple21 int int) (t2tb5 x) (t2tb5 y)) (not (= x empty3)))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 x)
  (non_empty_power (tuple21 int int) (t2tb5 y)))) )))

(declare-fun t2tb8 ((set (set Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set Bool)))) (sort (set1 (set1 bool)) (t2tb8 x))))

(declare-fun tb2t8 (uni) (set (set Bool)))

;; BridgeL
  (assert
  (forall ((i (set (set Bool))))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 bool)) j) (= (t2tb8 (tb2t8 j)) j)) :pattern (
  (t2tb8 (tb2t8 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Bool)) (y (set Bool)))
  (! (= (mem (set1 bool) (t2tb3 x) (non_empty_power bool (t2tb3 y)))
     (and (subset bool (t2tb3 x) (t2tb3 y)) (not (= x empty1)))) :pattern ((mem
  (set1 bool) (t2tb3 x) (non_empty_power bool (t2tb3 y)))) )))

(declare-fun t2tb7 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb7 x))))

(declare-fun tb2t7 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb7 (tb2t7 j)) j) :pattern ((t2tb7 (tb2t7 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem (set1 int) (t2tb x) (non_empty_power int (t2tb y)))
     (and (subset int (t2tb x) (t2tb y)) (not (= x empty2)))) :pattern ((mem
  (set1 int) (t2tb x) (non_empty_power int (t2tb y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni))
  (! (=> (sort (set1 a) x)
     (= (mem (set1 a) x (non_empty_power a y))
     (and (subset a x y) (not (= x (empty a)))))) :pattern ((mem
  (set1 a) x (non_empty_power a y))) ))))

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
  (forall ((a ty) (b ty))
  (forall ((r uni) (s uni) (t uni))
  (= (image b a r (union a s t)) (union b (image b a r s) (image b a r t))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 Int Int))) (x (tuple2 Int Int)))
  (= (image b (tuple21 int int) r
     (add (tuple21 int int) (t2tb6 x) (t2tb5 dom1))) (union b
                                                     (image b
                                                     (tuple21 int int) r
                                                     (add (tuple21 int int)
                                                     (t2tb6 x)
                                                     (t2tb5 empty3)))
                                                     (image b
                                                     (tuple21 int int) r
                                                     (t2tb5 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Bool)) (x Bool))
  (= (image b bool r (add bool (t2tb2 x) (t2tb3 dom1))) (union b
                                                        (image b bool r
                                                        (add bool (t2tb2 x)
                                                        (t2tb3 empty1)))
                                                        (image b bool r
                                                        (t2tb3 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Int)) (x Int))
  (= (image b int r (t2tb (add1 x dom1))) (union b
                                          (image b int r
                                          (t2tb (add1 x empty2)))
                                          (image b int r (t2tb dom1)))))))

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
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

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
  (= (tb2t5 (dom b (tuple21 int int) (empty (tuple21 (tuple21 int int) b)))) 
  empty3)))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t3 (dom b bool (empty (tuple21 bool b)))) empty1)))

;; dom_empty
  (assert (= (tb2t (dom int int (t2tb5 empty3))) empty2))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t (dom b int (empty (tuple21 int b)))) empty2)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x Int) (y uni))
  (= (tb2t (dom b int (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) f))) 
  (add1 x (tb2t (dom b int f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Int Int)) (y uni))
  (= (tb2t5
     (dom b (tuple21 int int)
     (add (tuple21 (tuple21 int int) b)
     (Tuple2 (tuple21 int int) b (t2tb6 x) y)
     (empty (tuple21 (tuple21 int int) b))))) (tb2t5
                                              (add (tuple21 int int)
                                              (t2tb6 x) (t2tb5 empty3)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni))
  (= (tb2t3
     (dom b bool
     (add (tuple21 bool b) (Tuple2 bool b (t2tb2 x) y)
     (empty (tuple21 bool b))))) (tb2t3 (add bool (t2tb2 x) (t2tb3 empty1)))))))

;; dom_singleton
  (assert
  (forall ((x Int) (y Int))
  (= (tb2t
     (dom int int
     (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
     (t2tb5 empty3)))) (add1 x empty2))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni))
  (= (tb2t
     (dom b int
     (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (empty (tuple21 int b))))) 
  (add1 x empty2)))))

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
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem int (t2tb1 x) (t2tb s)) (mem int (t2tb1 y) (t2tb t))) (mem
  (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 empty3))
  (infix_plmngt int int (t2tb s) (t2tb t))))))

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
  (forall ((x uni) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 a (tuple21 int int)))
  (add (tuple21 a (tuple21 int int)) (Tuple2 a (tuple21 int int) x (t2tb6 y))
  (empty (tuple21 a (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) a (add a x (empty a))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty3)))) :pattern ((add
                                                               (tuple21 a
                                                               (tuple21 
                                                               int int))
                                                               (Tuple2 a
                                                               (tuple21 
                                                               int int) x
                                                               (t2tb6 y))
                                                               (empty
                                                               (tuple21 a
                                                               (tuple21 
                                                               int int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Bool)) (! (mem (set1 (tuple21 a bool))
  (add (tuple21 a bool) (Tuple2 a bool x (t2tb2 y)) (empty (tuple21 a bool)))
  (infix_mnmngt bool a (add a x (empty a))
  (add bool (t2tb2 y) (t2tb3 empty1)))) :pattern ((add (tuple21 a bool)
                                                  (Tuple2 a bool x (t2tb2 y))
                                                  (empty (tuple21 a bool)))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Int)) (! (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))
  (infix_mnmngt int a (add a x (empty a)) (t2tb (add1 y empty2)))) :pattern (
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))) ))))

(declare-fun t2tb9 ((set (set (tuple2 (tuple2 Int Int) (tuple2 Int
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) (tuple21 int int)))) (t2tb9 x))))

(declare-fun tb2t9 (uni) (set (set (tuple2 (tuple2 Int Int) (tuple2 Int
  Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb9 (tb2t9 j)) j) :pattern ((t2tb9 (tb2t9 j))) )))

(declare-fun t2tb10 ((set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))) (sort
  (set1 (tuple21 (tuple21 int int) (tuple21 int int))) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb10 (tb2t10 j)) j) :pattern ((t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 ((tuple2 (tuple2 Int Int) (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 Int Int)))) (sort
  (tuple21 (tuple21 int int) (tuple21 int int)) (t2tb11 x))))

(declare-fun tb2t11 (uni) (tuple2 (tuple2 Int Int) (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 Int Int))))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb11 (tb2t11 j)) j) :pattern ((t2tb11 (tb2t11 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 (tuple21 int int) (tuple21 int int)))
  (add (tuple21 (tuple21 int int) (tuple21 int int))
  (Tuple2 (tuple21 int int) (tuple21 int int) (t2tb6 x) (t2tb6 y))
  (empty (tuple21 (tuple21 int int) (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty3))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t10
                                                               (add
                                                               (tuple21
                                                               (tuple21 
                                                               int int)
                                                               (tuple21 
                                                               int int))
                                                               (Tuple2
                                                               (tuple21 
                                                               int int)
                                                               (tuple21 
                                                               int int)
                                                               (t2tb6 x)
                                                               (t2tb6 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21 
                                                               int int)
                                                               (tuple21 
                                                               int int)))))) )))

(declare-fun t2tb12 ((set (set (tuple2 (tuple2 Int Int) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Bool))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) bool))) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (set (tuple2 (tuple2 Int Int) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Bool)))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 ((set (tuple2 (tuple2 Int Int) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Bool)))) (sort
  (set1 (tuple21 (tuple21 int int) bool)) (t2tb13 x))))

(declare-fun tb2t13 (uni) (set (tuple2 (tuple2 Int Int) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Bool))))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb13 (tb2t13 j)) j) :pattern ((t2tb13 (tb2t13 j))) )))

(declare-fun t2tb14 ((tuple2 (tuple2 Int Int) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Bool))) (sort
  (tuple21 (tuple21 int int) bool) (t2tb14 x))))

(declare-fun tb2t14 (uni) (tuple2 (tuple2 Int Int) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) Bool)))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y Bool)) (! (mem
  (set1 (tuple21 (tuple21 int int) bool))
  (add (tuple21 (tuple21 int int) bool)
  (Tuple2 (tuple21 int int) bool (t2tb6 x) (t2tb2 y))
  (empty (tuple21 (tuple21 int int) bool)))
  (infix_mnmngt bool (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty3))
  (add bool (t2tb2 y) (t2tb3 empty1)))) :pattern ((tb2t13
                                                  (add
                                                  (tuple21 (tuple21 int int)
                                                  bool)
                                                  (Tuple2 (tuple21 int int)
                                                  bool (t2tb6 x) (t2tb2 y))
                                                  (empty
                                                  (tuple21 (tuple21 int int)
                                                  bool))))) )))

(declare-fun t2tb15 ((set (set (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) int))) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (set (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

(declare-fun t2tb16 ((set (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))) (sort
  (set1 (tuple21 (tuple21 int int) int)) (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb16 (tb2t16 j)) j) :pattern ((t2tb16 (tb2t16 j))) )))

(declare-fun t2tb17 ((tuple2 (tuple2 Int Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int))) (sort
  (tuple21 (tuple21 int int) int) (t2tb17 x))))

(declare-fun tb2t17 (uni) (tuple2 (tuple2 Int Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) Int)))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 int int) int))
  (add (tuple21 (tuple21 int int) int)
  (Tuple2 (tuple21 int int) int (t2tb6 x) (t2tb1 y))
  (empty (tuple21 (tuple21 int int) int)))
  (infix_mnmngt int (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty3)) (t2tb (add1 y empty2)))) :pattern (
  (tb2t16
  (add (tuple21 (tuple21 int int) int)
  (Tuple2 (tuple21 int int) int (t2tb6 x) (t2tb1 y))
  (empty (tuple21 (tuple21 int int) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Int Int)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 int int) b))
  (add (tuple21 (tuple21 int int) b) (Tuple2 (tuple21 int int) b (t2tb6 x) y)
  (empty (tuple21 (tuple21 int int) b)))
  (infix_mnmngt b (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty3)) (add b y (empty b)))) :pattern (
  (add (tuple21 (tuple21 int int) b) (Tuple2 (tuple21 int int) b (t2tb6 x) y)
  (empty (tuple21 (tuple21 int int) b)))) ))))

(declare-fun t2tb18 ((set (set (tuple2 Bool (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 bool (tuple21 int int)))) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (set (tuple2 Bool (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 Int Int))))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb18 (tb2t18 j)) j) :pattern ((t2tb18 (tb2t18 j))) )))

(declare-fun t2tb19 ((set (tuple2 Bool (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 Int Int))))) (sort
  (set1 (tuple21 bool (tuple21 int int))) (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (tuple2 Bool (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 Int Int)))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

(declare-fun t2tb20 ((tuple2 Bool (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 Int Int)))) (sort
  (tuple21 bool (tuple21 int int)) (t2tb20 x))))

(declare-fun tb2t20 (uni) (tuple2 Bool (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 Int Int))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 bool (tuple21 int int)))
  (add (tuple21 bool (tuple21 int int))
  (Tuple2 bool (tuple21 int int) (t2tb2 x) (t2tb6 y))
  (empty (tuple21 bool (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) bool (add bool (t2tb2 x) (t2tb3 empty1))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t19
                                                               (add
                                                               (tuple21 
                                                               bool
                                                               (tuple21 
                                                               int int))
                                                               (Tuple2 
                                                               bool
                                                               (tuple21 
                                                               int int)
                                                               (t2tb2 x)
                                                               (t2tb6 y))
                                                               (empty
                                                               (tuple21 
                                                               bool
                                                               (tuple21 
                                                               int int)))))) )))

(declare-fun t2tb21 ((set (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Bool)))) (sort (set1 (tuple21 bool bool))
  (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Bool))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool bool)) j) (= (t2tb21 (tb2t21 j)) j)) :pattern (
  (t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((tuple2 Bool Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool Bool))) (sort (tuple21 bool bool) (t2tb22 x))))

(declare-fun tb2t22 (uni) (tuple2 Bool Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool Bool)))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool bool) j) (= (t2tb22 (tb2t22 j)) j)) :pattern (
  (t2tb22 (tb2t22 j))) )))

(declare-fun t2tb23 ((set (set (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool Bool))))) (sort
  (set1 (set1 (tuple21 bool bool))) (t2tb23 x))))

(declare-fun tb2t23 (uni) (set (set (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool Bool)))))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool bool))) j)
     (= (t2tb23 (tb2t23 j)) j)) :pattern ((t2tb23 (tb2t23 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y Bool)) (! (mem (set1 (tuple21 bool bool))
  (add (tuple21 bool bool) (Tuple2 bool bool (t2tb2 x) (t2tb2 y))
  (empty (tuple21 bool bool)))
  (infix_mnmngt bool bool (add bool (t2tb2 x) (t2tb3 empty1))
  (add bool (t2tb2 y) (t2tb3 empty1)))) :pattern ((tb2t21
                                                  (add (tuple21 bool bool)
                                                  (Tuple2 bool bool (t2tb2 x)
                                                  (t2tb2 y))
                                                  (empty (tuple21 bool bool))))) )))

(declare-fun t2tb24 ((set (set (tuple2 Bool Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool Int))))) (sort
  (set1 (set1 (tuple21 bool int))) (t2tb24 x))))

(declare-fun tb2t24 (uni) (set (set (tuple2 Bool Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool Int)))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb24 (tb2t24 j)) j) :pattern ((t2tb24 (tb2t24 j))) )))

(declare-fun t2tb25 ((set (tuple2 Bool Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Int)))) (sort (set1 (tuple21 bool int))
  (t2tb25 x))))

(declare-fun tb2t25 (uni) (set (tuple2 Bool Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Int))))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb25 (tb2t25 j)) j) :pattern ((t2tb25 (tb2t25 j))) )))

(declare-fun t2tb26 ((tuple2 Bool Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool Int))) (sort (tuple21 bool int) (t2tb26 x))))

(declare-fun tb2t26 (uni) (tuple2 Bool Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool Int)))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb26 (tb2t26 j)) j) :pattern ((t2tb26 (tb2t26 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y Int)) (! (mem (set1 (tuple21 bool int))
  (add (tuple21 bool int) (Tuple2 bool int (t2tb2 x) (t2tb1 y))
  (empty (tuple21 bool int)))
  (infix_mnmngt int bool (add bool (t2tb2 x) (t2tb3 empty1))
  (t2tb (add1 y empty2)))) :pattern ((tb2t25
                                     (add (tuple21 bool int)
                                     (Tuple2 bool int (t2tb2 x) (t2tb1 y))
                                     (empty (tuple21 bool int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni)) (! (mem (set1 (tuple21 bool b))
  (add (tuple21 bool b) (Tuple2 bool b (t2tb2 x) y) (empty (tuple21 bool b)))
  (infix_mnmngt b bool (add bool (t2tb2 x) (t2tb3 empty1))
  (add b y (empty b)))) :pattern ((add (tuple21 bool b)
                                  (Tuple2 bool b (t2tb2 x) y)
                                  (empty (tuple21 bool b)))) ))))

(declare-fun t2tb27 ((set (set (tuple2 Int (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 int int)))) (t2tb27 x))))

(declare-fun tb2t27 (uni) (set (set (tuple2 Int (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 Int Int))))))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb27 (tb2t27 j)) j) :pattern ((t2tb27 (tb2t27 j))) )))

(declare-fun t2tb28 ((set (tuple2 Int (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int Int))))) (sort
  (set1 (tuple21 int (tuple21 int int))) (t2tb28 x))))

(declare-fun tb2t28 (uni) (set (tuple2 Int (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int Int)))))
  (! (= (tb2t28 (t2tb28 i)) i) :pattern ((t2tb28 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb28 (tb2t28 j)) j) :pattern ((t2tb28 (tb2t28 j))) )))

(declare-fun t2tb29 ((tuple2 Int (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 Int Int)))) (sort
  (tuple21 int (tuple21 int int)) (t2tb29 x))))

(declare-fun tb2t29 (uni) (tuple2 Int (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 Int Int))))
  (! (= (tb2t29 (t2tb29 i)) i) :pattern ((t2tb29 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb29 (tb2t29 j)) j) :pattern ((t2tb29 (tb2t29 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 int (tuple21 int int)))
  (add (tuple21 int (tuple21 int int))
  (Tuple2 int (tuple21 int int) (t2tb1 x) (t2tb6 y))
  (empty (tuple21 int (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) int (t2tb (add1 x empty2))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t28
                                                               (add
                                                               (tuple21 
                                                               int
                                                               (tuple21 
                                                               int int))
                                                               (Tuple2 
                                                               int
                                                               (tuple21 
                                                               int int)
                                                               (t2tb1 x)
                                                               (t2tb6 y))
                                                               (empty
                                                               (tuple21 
                                                               int
                                                               (tuple21 
                                                               int int)))))) )))

(declare-fun t2tb30 ((set (set (tuple2 Int Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Bool))))) (sort
  (set1 (set1 (tuple21 int bool))) (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (set (tuple2 Int Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Bool)))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb30 (tb2t30 j)) j) :pattern ((t2tb30 (tb2t30 j))) )))

(declare-fun t2tb31 ((set (tuple2 Int Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Bool)))) (sort (set1 (tuple21 int bool))
  (t2tb31 x))))

(declare-fun tb2t31 (uni) (set (tuple2 Int Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Bool))))
  (! (= (tb2t31 (t2tb31 i)) i) :pattern ((t2tb31 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb31 (tb2t31 j)) j) :pattern ((t2tb31 (tb2t31 j))) )))

(declare-fun t2tb32 ((tuple2 Int Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Bool))) (sort (tuple21 int bool) (t2tb32 x))))

(declare-fun tb2t32 (uni) (tuple2 Int Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Bool)))
  (! (= (tb2t32 (t2tb32 i)) i) :pattern ((t2tb32 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb32 (tb2t32 j)) j) :pattern ((t2tb32 (tb2t32 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Bool)) (! (mem (set1 (tuple21 int bool))
  (add (tuple21 int bool) (Tuple2 int bool (t2tb1 x) (t2tb2 y))
  (empty (tuple21 int bool)))
  (infix_mnmngt bool int (t2tb (add1 x empty2))
  (add bool (t2tb2 y) (t2tb3 empty1)))) :pattern ((tb2t31
                                                  (add (tuple21 int bool)
                                                  (Tuple2 int bool (t2tb1 x)
                                                  (t2tb2 y))
                                                  (empty (tuple21 int bool))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 empty3))
  (infix_mnmngt int int (t2tb (add1 x empty2)) (t2tb (add1 y empty2)))) :pattern (
  (tb2t5
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 empty3)))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni)) (! (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (empty (tuple21 int b)))
  (infix_mnmngt b int (t2tb (add1 x empty2)) (add b y (empty b)))) :pattern (
  (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (empty (tuple21 int b)))) ))))

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
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem a a1
  (dom b a f))) (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

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
  (forall ((x Int) (y Int))
  (= (tb2t1
     (apply int int
     (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
     (t2tb5 empty3)) (t2tb1 x))) y)))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b))) x) y)))))

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
  (= (seq_length a n s) (infix_mnmngt a int (t2tb (mk 1 n)) s)))))

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
  (infix_mnmngt a int (t2tb (mk 1 (size a r))) s))))))

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
  (forall ((s (set (tuple2 Int Int)))) (is_finite_subset (tuple21 int int)
  (t2tb5 empty3) (t2tb5 s) 0)))

;; Empty
  (assert
  (forall ((s (set Bool))) (is_finite_subset bool (t2tb3 empty1) (t2tb3 s)
  0)))

;; Empty
  (assert
  (forall ((s (set Int))) (is_finite_subset int (t2tb empty2) (t2tb s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (=> (mem int (t2tb1 x) (t2tb s2))
  (=> (mem int (t2tb1 x) (t2tb s1)) (is_finite_subset int (t2tb (add1 x s1))
  (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (=> (mem int (t2tb1 x) (t2tb s2))
  (=> (not (mem int (t2tb1 x) (t2tb s1))) (is_finite_subset int
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
  (forall ((z (set (tuple2 Int Int))) (z1 (set (tuple2 Int Int))) (z2 Int))
  (=> (is_finite_subset (tuple21 int int) (t2tb5 z) (t2tb5 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 Int Int))))
  (and (and (= z empty3) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))) (c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb5 s1) (t2tb5 s2) c)
  (and (mem (tuple21 int int) (t2tb6 x) (t2tb5 s2))
  (and (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1))
  (and
  (and (= z (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))) (= z1 s2))
  (= z2 c)))))))
  (exists ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))) (c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb5 s1) (t2tb5 s2) c)
  (and (mem (tuple21 int int) (t2tb6 x) (t2tb5 s2))
  (and (not (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1)))
  (and
  (and (= z (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))) (= z1 s2))
  (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Bool)) (z1 (set Bool)) (z2 Int))
  (=> (is_finite_subset bool (t2tb3 z) (t2tb3 z1) z2)
  (or
  (or (exists ((s (set Bool))) (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb3 s1) (t2tb3 s2) c)
  (and (mem bool (t2tb2 x) (t2tb3 s2))
  (and (mem bool (t2tb2 x) (t2tb3 s1))
  (and (and (= z (tb2t3 (add bool (t2tb2 x) (t2tb3 s1)))) (= z1 s2))
  (= z2 c)))))))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb3 s1) (t2tb3 s2) c)
  (and (mem bool (t2tb2 x) (t2tb3 s2))
  (and (not (mem bool (t2tb2 x) (t2tb3 s1)))
  (and (and (= z (tb2t3 (add bool (t2tb2 x) (t2tb3 s1)))) (= z1 s2))
  (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb z) (t2tb z1) z2)
  (or
  (or (exists ((s (set Int))) (and (and (= z empty2) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (and (mem int (t2tb1 x) (t2tb s2))
  (and (mem int (t2tb1 x) (t2tb s1))
  (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (and (mem int (t2tb1 x) (t2tb s2))
  (and (not (mem int (t2tb1 x) (t2tb s1)))
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
  (=> (<= a b) (is_finite_subset int (t2tb (mk a b)) (t2tb integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb (mk a b)) (t2tb integer) 0))))

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
  (forall ((s (set (tuple2 Int Int)))) (mem (set1 (tuple21 int int))
  (t2tb5 empty3) (finite_subsets (tuple21 int int) (t2tb5 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Bool))) (mem (set1 bool) (t2tb3 empty1)
  (finite_subsets bool (t2tb3 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Int))) (mem (set1 int) (t2tb empty2)
  (finite_subsets int (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (=> (mem int (t2tb1 x) (t2tb s2)) (mem (set1 int) (t2tb (add1 x s1))
  (finite_subsets int (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int))))
  (=> (mem (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s2)))
  (or (= s1 empty3)
  (exists ((x (tuple2 Int Int)) (s3 (set (tuple2 Int Int))))
  (and (= s1 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s3)))) (mem
  (set1 (tuple21 int int)) (t2tb5 s3)
  (finite_subsets (tuple21 int int) (t2tb5 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (=> (mem (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s2)))
  (or (= s1 empty1)
  (exists ((x Bool) (s3 (set Bool)))
  (and (= s1 (tb2t3 (add bool (t2tb2 x) (t2tb3 s3)))) (mem (set1 bool)
  (t2tb3 s3) (finite_subsets bool (t2tb3 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (or (= s1 empty2)
  (exists ((x Int) (s3 (set Int)))
  (and (= s1 (add1 x s3)) (mem (set1 int) (t2tb s3)
  (finite_subsets int (t2tb s2)))))))))

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
  (forall ((s (set (tuple2 Int Int))) (x (set (tuple2 Int Int))))
  (= (mem (set1 (tuple21 int int)) (t2tb5 x)
  (non_empty_finite_subsets (tuple21 int int) (t2tb5 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb5 x) (t2tb5 s) c)
  (not (= x empty3)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Bool)) (x (set Bool)))
  (= (mem (set1 bool) (t2tb3 x) (non_empty_finite_subsets bool (t2tb3 s)))
  (exists ((c Int))
  (and (is_finite_subset bool (t2tb3 x) (t2tb3 s) c) (not (= x empty1)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem (set1 int) (t2tb x) (non_empty_finite_subsets int (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset int (t2tb x) (t2tb s) c) (not (= x empty2)))))))

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

(declare-fun card1 ((set Bool)) Int)

(declare-fun card2 ((set Int)) Int)

(declare-fun card3 ((set (tuple2 Int Int))) Int)

;; card_def
  (assert
  (forall ((s (set (tuple2 Int Int))) (x (set (tuple2 Int Int))) (c Int))
  (=> (is_finite_subset (tuple21 int int) (t2tb5 x) (t2tb5 s) c)
  (= (card3 x) c))))

;; card_def
  (assert
  (forall ((s (set Bool)) (x (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb3 x) (t2tb3 s) c) (= (card1 x) c))))

;; card_def
  (assert
  (forall ((s (set Int)) (x (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb x) (t2tb s) c) (= (card2 x) c))))

;; card_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (c Int))
  (=> (is_finite_subset a x s c) (= (card a x) c)))))

;; card_Empty
  (assert (= (card3 empty3) 0))

;; card_Empty
  (assert (= (card1 empty1) 0))

;; card_Empty
  (assert (= (card2 empty2) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))))
  (! (=> (mem (set1 (tuple21 int int)) (t2tb5 s1)
     (finite_subsets (tuple21 int int) (t2tb5 s2)))
     (=> (not (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1)))
     (= (card3 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))) (+ 
     (card3 s1) 1)))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s2)))
  (card3 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1))))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s2)))
     (=> (not (mem bool (t2tb2 x) (t2tb3 s1)))
     (= (card1 (tb2t3 (add bool (t2tb2 x) (t2tb3 s1)))) (+ (card1 s1) 1)))) :pattern ((mem
  (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s2)))
  (card1 (tb2t3 (add bool (t2tb2 x) (t2tb3 s1))))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
     (=> (not (mem int (t2tb1 x) (t2tb s1)))
     (= (card2 (add1 x s1)) (+ (card2 s1) 1)))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (card2 (add1 x s1))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))))
  (! (=> (mem (set1 (tuple21 int int)) (t2tb5 s1)
     (finite_subsets (tuple21 int int) (t2tb5 s2)))
     (=> (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1))
     (= (card3 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))) 
     (card3 s1)))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s2)))
  (card3 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1))))) )))

;; card_Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s2)))
     (=> (mem bool (t2tb2 x) (t2tb3 s1))
     (= (card1 (tb2t3 (add bool (t2tb2 x) (t2tb3 s1)))) (card1 s1)))) :pattern ((mem
  (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s2)))
  (card1 (tb2t3 (add bool (t2tb2 x) (t2tb3 s1))))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
     (=> (mem int (t2tb1 x) (t2tb s1)) (= (card2 (add1 x s1)) (card2 s1)))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (card2 (add1 x s1))) )))

;; card_Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (mem a x s1) (= (card a (add a x s1)) (card a s1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Union
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int)))
  (s3 (set (tuple2 Int Int))))
  (! (=> (mem (set1 (tuple21 int int)) (t2tb5 s1)
     (finite_subsets (tuple21 int int) (t2tb5 s3)))
     (=> (mem (set1 (tuple21 int int)) (t2tb5 s2)
     (finite_subsets (tuple21 int int) (t2tb5 s3)))
     (=> (is_empty (tuple21 int int)
     (inter (tuple21 int int) (t2tb5 s1) (t2tb5 s2)))
     (= (card3 (tb2t5 (union (tuple21 int int) (t2tb5 s1) (t2tb5 s2)))) (+ 
     (card3 s1) (card3 s2)))))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s3))) (mem
  (set1 (tuple21 int int)) (t2tb5 s2)
  (finite_subsets (tuple21 int int) (t2tb5 s3)))
  (card3 (tb2t5 (union (tuple21 int int) (t2tb5 s1) (t2tb5 s2))))) )))

;; card_Union
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)) (s3 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s3)))
     (=> (mem (set1 bool) (t2tb3 s2) (finite_subsets bool (t2tb3 s3)))
     (=> (is_empty bool (inter bool (t2tb3 s1) (t2tb3 s2)))
     (= (card1 (tb2t3 (union bool (t2tb3 s1) (t2tb3 s2)))) (+ (card1 s1) 
     (card1 s2)))))) :pattern ((mem
  (set1 bool) (t2tb3 s1) (finite_subsets bool (t2tb3 s3))) (mem (set1 bool)
  (t2tb3 s2) (finite_subsets bool (t2tb3 s3)))
  (card1 (tb2t3 (union bool (t2tb3 s1) (t2tb3 s2))))) )))

;; card_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s3)))
     (=> (mem (set1 int) (t2tb s2) (finite_subsets int (t2tb s3)))
     (=> (is_empty int (inter int (t2tb s1) (t2tb s2)))
     (= (card2 (tb2t (union int (t2tb s1) (t2tb s2)))) (+ (card2 s1) 
     (card2 s2)))))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s3))) (mem (set1 int)
  (t2tb s2) (finite_subsets int (t2tb s3)))
  (card2 (tb2t (union int (t2tb s1) (t2tb s2))))) )))

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
  (= (relations b a u v) (power1 (tuple21 a b) (times b a u v))))))

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
  (= (mem (set1 (tuple21 a b)) r (power1 (tuple21 a b) (times b a u v)))
  (subset (tuple21 a b) r (times b a u v))))))

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
  (forall ((s uni) (x uni) (y (tuple2 Int Int)))
  (! (=> (mem a x s)
     (= (tb2t6
        (apply (tuple21 int int) a
        (times (tuple21 int int) a s
        (add (tuple21 int int) (t2tb6 y) (t2tb5 empty3))) x)) y)) :pattern (
  (tb2t6
  (apply (tuple21 int int) a
  (times (tuple21 int int) a s
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty3))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Bool))
  (! (=> (mem a x s)
     (= (tb2t2
        (apply bool a (times bool a s (add bool (t2tb2 y) (t2tb3 empty1))) x)) y)) :pattern (
  (tb2t2
  (apply bool a (times bool a s (add bool (t2tb2 y) (t2tb3 empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Int))
  (! (=> (mem a x s)
     (= (tb2t1 (apply int a (times int a s (t2tb (add1 y empty2))) x)) y)) :pattern (
  (tb2t1 (apply int a (times int a s (t2tb (add1 y empty2))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (x uni) (y uni))
  (! (=> (sort b y)
     (=> (mem a x s) (= (apply b a (times b a s (add b y (empty b))) x) y))) :pattern (
  (apply b a (times b a s (add b y (empty b))) x)) ))))

(declare-fun range_restriction (ty ty uni uni) uni)

;; range_restriction_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (range_restriction b a x x1)))))

;; range_restriction_def
  (assert
  (forall ((e1 ty) (e2 ty))
  (forall ((x uni) (y uni) (r uni) (f uni))
  (=> (subset e2 f (ran e2 e1 r))
  (= (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) (range_restriction e2 e1 r f))
  (and (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) r) (mem e2 y f)))))))

(declare-fun range_substraction (ty ty uni uni) uni)

;; range_substraction_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (range_substraction b a x x1)))))

;; range_substraction_def
  (assert
  (forall ((e1 ty) (e2 ty))
  (forall ((x uni) (y uni) (r uni) (f uni))
  (= (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) (range_substraction e2 e1 r f))
  (and (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) r) (not (mem e2 y f)))))))

(declare-fun domain_restriction (ty ty uni uni) uni)

;; domain_restriction_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (domain_restriction b a x x1)))))

;; domain_restriction_def
  (assert
  (forall ((e1 ty) (e2 ty))
  (forall ((x uni) (y uni) (r uni) (f uni))
  (= (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) (domain_restriction e2 e1 f r))
  (and (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) r) (mem e1 x f))))))

(declare-fun domain_substraction (ty ty uni uni) uni)

;; domain_substraction_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (domain_substraction b a x x1)))))

;; domain_substraction_def
  (assert
  (forall ((e1 ty) (e2 ty))
  (forall ((x uni) (y uni) (r uni) (f uni))
  (=> (subset e1 f (dom e2 e1 r))
  (= (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) (domain_substraction e2 e1 f r))
  (and (mem (tuple21 e1 e2) (Tuple2 e1 e2 x y) r) (not (mem e1 x f))))))))

(declare-fun infix_lspl (ty ty uni uni) uni)

;; infix <+_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (infix_lspl b a x x1)))))

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
  (forall ((a ty) (b ty))
  (forall ((f uni) (g uni))
  (! (= (dom b a (infix_lspl b a f g)) (union a (dom b a f) (dom b a g))) :pattern (
  (dom b a (infix_lspl b a f g))) ))))

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

(declare-fun insert_in_front (ty uni uni) uni)

;; insert_in_front_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 int a))
  (insert_in_front a x x1)))))

(declare-fun insert_at_tail (ty uni uni) uni)

;; insert_at_tail_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 int a))
  (insert_at_tail a x x1)))))

(declare-fun tail (ty uni) uni)

;; tail_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (tuple21 int a)) (tail a x)))))

(declare-fun last (ty uni) uni)

;; last_sort
  (assert (forall ((a ty)) (forall ((x uni)) (sort a (last a x)))))

(declare-fun first (ty uni) uni)

;; first_sort
  (assert (forall ((a ty)) (forall ((x uni)) (sort a (first a x)))))

(declare-fun front (ty uni) uni)

;; front_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (tuple21 int a)) (front a x)))))

(declare-fun concatenation (ty uni uni) uni)

;; concatenation_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 int a))
  (concatenation a x x1)))))

(declare-fun conc (ty uni) uni)

;; conc_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (tuple21 int a)) (conc a x)))))

(declare-fun uninterpreted_type () ty)

(declare-fun anon_set_1 () (set Int))

;; anon_set_1_def
  (assert
  (forall ((v_xx Int))
  (= (mem int (t2tb1 v_xx) (t2tb anon_set_1))
  (and
  (and
  (and (and (mem int (t2tb1 v_xx) (t2tb integer)) (<= v_xx 2147483647))
  (<= (- 2147483647) v_xx)) (<= (- 1) v_xx)) (<= v_xx 5)))))

(declare-fun anon_set_2 () (set Bool))

;; anon_set_2_def
  (assert
  (forall ((v_xx Bool))
  (= (mem bool (t2tb2 v_xx) (t2tb3 anon_set_2)) (= v_xx true))))

(declare-fun anon_set_3 (Int) (set Int))

;; anon_set_3_def
  (assert
  (forall ((v_yy Int) (v_zz Int))
  (= (mem int (t2tb1 v_zz) (t2tb (anon_set_3 v_yy)))
  (and (and (mem int (t2tb1 v_zz) (t2tb integer)) (<= 0 v_zz))
  (<= v_zz v_yy)))))

(declare-fun anon_UNION_4 ((set Int)) (set Int))

;; anon_UNION_4_def
  (assert
  (forall ((v_GG (set Int)) (v_anon_UNION_4 Int))
  (= (mem int (t2tb1 v_anon_UNION_4) (t2tb (anon_UNION_4 v_GG)))
  (exists ((v_yy Int))
  (and (mem int (t2tb1 v_yy) (t2tb v_GG)) (mem int (t2tb1 v_anon_UNION_4)
  (t2tb (anon_set_3 v_yy))))))))

(declare-fun anon_set_5 () (set Int))

;; anon_set_5_def
  (assert
  (forall ((v_xx Int))
  (= (mem int (t2tb1 v_xx) (t2tb anon_set_5))
  (and (and (mem int (t2tb1 v_xx) (t2tb integer)) (<= 2 v_xx)) (<= v_xx 4)))))

(declare-fun anon_set_6 () (set Int))

;; anon_set_6_def
  (assert
  (forall ((v_xx Int))
  (= (mem int (t2tb1 v_xx) (t2tb anon_set_6))
  (and (and (mem int (t2tb1 v_xx) (t2tb integer)) (<= 2 v_xx)) (<= v_xx 4)))))

(declare-fun anon_set_7 (Int) (set Int))

;; anon_set_7_def
  (assert
  (forall ((v_yy Int) (v_zz Int))
  (= (mem int (t2tb1 v_zz) (t2tb (anon_set_7 v_yy)))
  (and (and (mem int (t2tb1 v_zz) (t2tb integer)) (<= 0 v_zz))
  (<= v_zz v_yy)))))

(declare-fun anon_UNION_8 ((set Int)) (set Int))

;; anon_UNION_8_def
  (assert
  (forall ((v_GG (set Int)) (v_anon_UNION_8 Int))
  (= (mem int (t2tb1 v_anon_UNION_8) (t2tb (anon_UNION_8 v_GG)))
  (exists ((v_yy Int))
  (and (mem int (t2tb1 v_yy) (t2tb v_GG)) (mem int (t2tb1 v_anon_UNION_8)
  (t2tb (anon_set_7 v_yy))))))))

(declare-fun anon_set_9 (Int) (set Int))

;; anon_set_9_def
  (assert
  (forall ((v_vv Int) (v_xx Int))
  (= (mem int (t2tb1 v_xx) (t2tb (anon_set_9 v_vv)))
  (and
  (and
  (and (and (mem int (t2tb1 v_xx) (t2tb integer)) (<= v_xx 2147483647))
  (<= (- 2147483647) v_xx)) (<= (- 1) v_xx)) (<= v_xx v_vv)))))

(declare-fun anon_set_10 (Int) (set Int))

;; anon_set_10_def
  (assert
  (forall ((v_vv Int) (v_xx Int))
  (= (mem int (t2tb1 v_xx) (t2tb (anon_set_10 v_vv)))
  (and
  (and
  (and (and (mem int (t2tb1 v_xx) (t2tb integer)) (<= v_xx 2147483647))
  (<= (- 2147483647) v_xx)) (<= (- 1) v_xx)) (<= v_xx v_vv)))))

(declare-fun f1 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f1_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f1 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG)
  (and
  (and
  (and
  (and (infix_eqeq int (t2tb v_comprehension_set) (t2tb anon_set_1))
  (infix_eqeq (tuple21 int int) (t2tb5 v_relation)
  (union (tuple21 int int)
  (add (tuple21 int int) (Tuple2 int int (t2tb1 3) (t2tb1 6)) (t2tb5 empty3))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 4) (t2tb1 8)) (t2tb5 empty3)))))
  (infix_eqeq bool (t2tb3 v_another_set) (t2tb3 anon_set_2))) (infix_eqeq 
  int (t2tb v_simple_set)
  (union int (union int (t2tb (add1 1 empty2)) (t2tb (add1 2 empty2)))
  (t2tb (add1 3 empty2))))) (infix_eqeq int (t2tb v_GG)
  (union int (t2tb (add1 2 empty2)) (t2tb (add1 4 empty2))))))))

(declare-fun f4 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f4_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f4 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG)
  (and (mem (set1 int) (t2tb v_aa) (power1 int (t2tb v_INT))) (mem (set1 int)
  (t2tb v_aa) (power1 int (t2tb v_comprehension_set)))))))

(declare-fun f6 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f6_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f6 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG) (infix_eqeq int (t2tb (anon_UNION_4 v_GG))
  (union int
  (union int
  (union int (union int (t2tb (add1 0 empty2)) (t2tb (add1 1 empty2)))
  (t2tb (add1 2 empty2))) (t2tb (add1 3 empty2))) (t2tb (add1 4 empty2)))))))

(declare-fun f8 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f8_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f8 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG) (= (card2 v_simple_set) 3))))

(declare-fun f12 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f12_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f12 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG) (infix_eqeq int
  (image int int (t2tb5 v_relation) (t2tb anon_set_5))
  (union int (t2tb (add1 6 empty2)) (t2tb (add1 8 empty2)))))))

(declare-fun f15 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f15_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f15 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG)
  (and
  (and
  (and
  (and (mem int (t2tb1 3) (t2tb v_comprehension_set)) (infix_eqeq int
  (image int int (t2tb5 v_relation) (t2tb anon_set_6))
  (union int (t2tb (add1 6 empty2)) (t2tb (add1 8 empty2)))))
  (= (card2 (add1 1 empty2)) 1)) (= (card2 v_simple_set) 3)) (infix_eqeq 
  int (t2tb (anon_UNION_8 v_GG))
  (union int
  (union int
  (union int (union int (t2tb (add1 0 empty2)) (t2tb (add1 1 empty2)))
  (t2tb (add1 2 empty2))) (t2tb (add1 3 empty2))) (t2tb (add1 4 empty2))))))))

(declare-fun f16 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f16_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f16 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG)
  (and
  (and
  (and (and (mem int (t2tb1 v_vv) (t2tb integer)) (<= v_vv 2147483647))
  (<= (- 2147483647) v_vv)) (<= (- 1) v_vv)) (<= v_vv 5)))))

(declare-fun f18 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f18_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f18 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG) (mem (set1 int)
  (union int (t2tb v_aa) (t2tb (anon_set_9 v_vv)))
  (power1 int (t2tb v_INT))))))

(declare-fun f20 (Int (set Int) (set (tuple2 Int Int)) (set Int) (set Bool)
  (set Int) (set Int) (set Int)) Bool)

;; f20_def
  (assert
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (= (f20 v_vv v_simple_set v_relation v_comprehension_set v_another_set v_aa
  v_INT v_GG) (mem (set1 int)
  (union int (t2tb v_aa) (t2tb (anon_set_10 v_vv)))
  (power1 int (t2tb v_comprehension_set))))))

(assert
;; AssertionLemmas_3
 ;; File "POwhy_bpo2why/basic/Operators.why", line 290, characters 7-24
  (not
  (forall ((v_vv Int) (v_simple_set (set Int)) (v_relation (set (tuple2 Int
  Int))) (v_comprehension_set (set Int)) (v_another_set (set Bool))
  (v_aa (set Int)) (v_INT (set Int)) (v_GG (set Int)))
  (=>
  (and (f1 v_vv v_simple_set v_relation v_comprehension_set v_another_set
  v_aa v_INT v_GG) (f4 v_vv v_simple_set v_relation v_comprehension_set
  v_another_set v_aa v_INT v_GG)) (= (card2 (add1 1 empty2)) 1)))))
(check-sat)