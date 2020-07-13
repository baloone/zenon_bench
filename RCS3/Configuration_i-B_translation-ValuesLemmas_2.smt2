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

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (Int (set Int)) Bool)

(declare-fun mem2 ((set (tuple2 Int Int)) (set (set (tuple2 Int Int)))) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

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

;; infix ==_def
  (assert
  (forall ((s1 (set (set (tuple2 Int Int)))) (s2 (set (set (tuple2 Int
  Int)))))
  (= (infix_eqeq (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2))
  (forall ((x (set (tuple2 Int Int)))) (= (mem2 x s1) (mem2 x s2))))))

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

;; infix ==_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (infix_eqeq int (t2tb s1) (t2tb s2))
  (forall ((x Int)) (= (mem1 x s1) (mem1 x s2))))))

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
  (forall ((s1 (set (set (tuple2 Int Int)))) (s2 (set (set (tuple2 Int
  Int)))))
  (= (subset (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2))
  (forall ((x (set (tuple2 Int Int)))) (=> (mem2 x s1) (mem2 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (subset int (t2tb s1) (t2tb s2))
  (forall ((x Int)) (=> (mem1 x s1) (mem1 x s2))))))

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

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set (set (tuple2 Int Int)))))
  (= (is_empty (set1 (tuple21 int int)) (t2tb4 s))
  (forall ((x (set (tuple2 Int Int)))) (not (mem2 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set Int)))
  (= (is_empty int (t2tb s)) (forall ((x Int)) (not (mem1 x s))))))

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (set (tuple2 Int Int))))
  (not (mem2 x (tb2t4 (empty (set1 (tuple21 int int))))))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem1 x (tb2t (empty int))))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

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

;; add_def1
  (assert
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (forall ((s (set (set (tuple2 Int Int)))))
  (= (mem2 x (tb2t4 (add (set1 (tuple21 int int)) (t2tb5 y) (t2tb4 s))))
  (or (= x y) (mem2 x s))))))

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

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int)))
  (= (mem1 x (tb2t (add int (t2tb1 y) (t2tb s)))) (or (= x y) (mem1 x s))))))

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
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int)))
  (s (set (set (tuple2 Int Int)))))
  (= (mem2 x (tb2t4 (remove (set1 (tuple21 int int)) (t2tb5 y) (t2tb4 s))))
  (and (not (= x y)) (mem2 x s)))))

;; remove_def1
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem1 x (tb2t (remove int (t2tb1 y) (t2tb s))))
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
  (forall ((x (set (tuple2 Int Int))) (s (set (set (tuple2 Int Int)))))
  (=> (mem2 x s)
  (= (tb2t4
     (add (set1 (tuple21 int int)) (t2tb5 x)
     (remove (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s)))) s))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem1 x s)
  (= (tb2t (add int (t2tb1 x) (remove int (t2tb1 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

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
  (forall ((s1 (set (set (tuple2 Int Int)))) (s2 (set (set (tuple2 Int
  Int)))) (x (set (tuple2 Int Int))))
  (= (mem2 x (tb2t4 (union (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2))))
  (or (mem2 x s1) (mem2 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t (union int (t2tb s1) (t2tb s2))))
  (or (mem1 x s1) (mem1 x s2)))))

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
  (forall ((s1 (set (set (tuple2 Int Int)))) (s2 (set (set (tuple2 Int
  Int)))) (x (set (tuple2 Int Int))))
  (= (mem2 x (tb2t4 (inter (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2))))
  (and (mem2 x s1) (mem2 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t (inter int (t2tb s1) (t2tb s2))))
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
  (forall ((s1 (set (set (tuple2 Int Int)))) (s2 (set (set (tuple2 Int
  Int)))) (x (set (tuple2 Int Int))))
  (= (mem2 x (tb2t4 (diff (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2))))
  (and (mem2 x s1) (not (mem2 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t (diff int (t2tb s1) (t2tb s2))))
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
  (forall ((s (set (set (tuple2 Int Int)))))
  (=> (not (is_empty (set1 (tuple21 int int)) (t2tb4 s))) (mem2
  (tb2t5 (choose (set1 (tuple21 int int)) (t2tb4 s))) s))))

;; choose_def
  (assert
  (forall ((s (set Int)))
  (=> (not (is_empty int (t2tb s))) (mem1 (tb2t1 (choose int (t2tb s))) s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert
  (forall ((x (set (tuple2 Int Int)))) (mem2 x
  (tb2t4 (all (set1 (tuple21 int int)))))))

;; all_def
  (assert (forall ((x Int)) (mem1 x (tb2t (all int)))))

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

;; mem_integer
  (assert (forall ((x Int)) (mem1 x integer)))

(declare-fun natural () (set Int))

;; mem_natural
  (assert (forall ((x Int)) (= (mem1 x natural) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert (forall ((x Int)) (= (mem1 x natural1) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int)) (= (mem1 x nat) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int)) (= (mem1 x nat1) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem1 x bounded_int) (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem1 x (mk a b)) (and (<= a x) (<= x b))) :pattern ((mem1 x
  (mk a b))) )))

;; interval_empty
  (assert
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t (empty int))))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b) (= (mk a b) (tb2t (add int (t2tb1 b) (t2tb (mk a (- b 1)))))))))

(declare-fun power1 (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power1 a x)))))

;; mem_power
  (assert
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (! (= (mem2 x (tb2t4 (power1 (tuple21 int int) (t2tb5 y)))) (subset
     (tuple21 int int) (t2tb5 x) (t2tb5 y))) :pattern ((mem2
  x (tb2t4 (power1 (tuple21 int int) (t2tb5 y))))) )))

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

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (! (= (mem2 x (tb2t4 (non_empty_power (tuple21 int int) (t2tb5 y))))
     (and (subset (tuple21 int int) (t2tb5 x) (t2tb5 y))
     (not (= x (tb2t5 (empty (tuple21 int int))))))) :pattern ((mem2
  x (tb2t4 (non_empty_power (tuple21 int int) (t2tb5 y))))) )))

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
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set (tuple2 Int Int)))))
  (and
  (=> (mem (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (relation (set1 (tuple21 int int)) a s (t2tb4 t)))
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (=>
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) f)
  (and (mem a x s) (mem2 y t))))) (mem
  (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (relation (set1 (tuple21 int int)) a s (t2tb4 t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (relation int a s (t2tb t)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f)
  (and (mem a x s) (mem1 y t))))) (mem (set1 (tuple21 a int)) f
  (relation int a s (t2tb t))))))))

(declare-fun t2tb18 ((set (set (tuple2 (set (tuple2 Int Int))
  (set (tuple2 Int Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int
  Int))))))) (sort
  (set1 (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))))
  (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (set (tuple2 (set (tuple2 Int Int))
  (set (tuple2 Int Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int
  Int))))))) (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb18 (tb2t18 j)) j) :pattern ((t2tb18 (tb2t18 j))) )))

(declare-fun t2tb19 ((set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int))))))
  (sort (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
  (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (tuple2 (set (tuple2 Int Int))
  (set (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int))))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

(declare-fun t2tb20 ((tuple2 (set (tuple2 Int Int)) (set (tuple2 Int
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int))))) (sort
  (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))) (t2tb20 x))))

(declare-fun tb2t20 (uni) (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int
  Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int)))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int)))))
  (s (set (set (tuple2 Int Int)))) (t (set (set (tuple2 Int Int)))))
  (= (mem (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
  (t2tb19 f)
  (relation (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 s)
  (t2tb4 t)))
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y)) (t2tb19 f)) (and (mem2 x s) (mem2 y t)))))))

(declare-fun t2tb21 ((set (set (tuple2 (set (tuple2 Int Int)) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 Int Int)) Int))))) (sort
  (set1 (set1 (tuple21 (set1 (tuple21 int int)) int))) (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (set (tuple2 (set (tuple2 Int Int)) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 Int Int)) Int)))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb21 (tb2t21 j)) j) :pattern ((t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((set (tuple2 (set (tuple2 Int Int)) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 Int Int)) Int)))) (sort
  (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 x))))

(declare-fun tb2t22 (uni) (set (tuple2 (set (tuple2 Int Int)) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 Int Int)) Int))))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb22 (tb2t22 j)) j) :pattern ((t2tb22 (tb2t22 j))) )))

(declare-fun t2tb23 ((tuple2 (set (tuple2 Int Int)) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 Int Int)) Int))) (sort
  (tuple21 (set1 (tuple21 int int)) int) (t2tb23 x))))

(declare-fun tb2t23 (uni) (tuple2 (set (tuple2 Int Int)) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 Int Int)) Int)))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb23 (tb2t23 j)) j) :pattern ((t2tb23 (tb2t23 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 Int Int)) Int)))
  (s (set (set (tuple2 Int Int)))) (t (set Int)))
  (= (mem (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 f)
  (relation int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t)))
  (forall ((x (set (tuple2 Int Int))) (y Int))
  (=> (mem (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y)) (t2tb22 f))
  (and (mem2 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set (tuple2 Int Int)))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (relation b (set1 (tuple21 int int)) (t2tb4 s) t))
  (forall ((x (set (tuple2 Int Int))) (y uni))
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (=>
  (forall ((x (set (tuple2 Int Int))) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) f)
  (and (mem2 x s) (mem b y t))))) (mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (relation b (set1 (tuple21 int int)) (t2tb4 s) t)))))))

(declare-fun t2tb24 ((tuple2 Int (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (set (tuple2 Int Int))))) (sort
  (tuple21 int (set1 (tuple21 int int))) (t2tb24 x))))

(declare-fun tb2t24 (uni) (tuple2 Int (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (set (tuple2 Int Int)))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb24 (tb2t24 j)) j) :pattern ((t2tb24 (tb2t24 j))) )))

(declare-fun t2tb25 ((set (set (tuple2 Int (set (tuple2 Int Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (set (tuple2 Int Int))))))) (sort
  (set1 (set1 (tuple21 int (set1 (tuple21 int int))))) (t2tb25 x))))

(declare-fun tb2t25 (uni) (set (set (tuple2 Int (set (tuple2 Int Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (set (tuple2 Int Int)))))))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb25 (tb2t25 j)) j) :pattern ((t2tb25 (tb2t25 j))) )))

(declare-fun t2tb26 ((set (tuple2 Int (set (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (set (tuple2 Int Int)))))) (sort
  (set1 (tuple21 int (set1 (tuple21 int int)))) (t2tb26 x))))

(declare-fun tb2t26 (uni) (set (tuple2 Int (set (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (set (tuple2 Int Int))))))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb26 (tb2t26 j)) j) :pattern ((t2tb26 (tb2t26 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int (set (tuple2 Int Int))))) (s (set Int))
  (t (set (set (tuple2 Int Int)))))
  (= (mem (set1 (tuple21 int (set1 (tuple21 int int)))) (t2tb26 f)
  (relation (set1 (tuple21 int int)) int (t2tb s) (t2tb4 t)))
  (forall ((x Int) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y)) (t2tb26 f))
  (and (mem1 x s) (mem2 y t)))))))

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

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (relation int int (t2tb s) (t2tb t))))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 f))
  (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (relation b int (t2tb s) t))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) f)
  (and (mem1 x s) (mem b y t))))) (mem (set1 (tuple21 int b)) f
  (relation b int (t2tb s) t)))))))

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
  (forall ((r uni) (dom1 uni) (y (set (tuple2 Int Int))))
  (! (and
     (=> (mem2 y (tb2t4 (image (set1 (tuple21 int int)) a r dom1)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom1) (mem (tuple21 a (set1 (tuple21 int int)))
     (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom1) (mem (tuple21 a (set1 (tuple21 int int)))
     (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) r))) (mem2 y
     (tb2t4 (image (set1 (tuple21 int int)) a r dom1))))) :pattern ((mem2
  y (tb2t4 (image (set1 (tuple21 int int)) a r dom1)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom1 uni) (y Int))
  (! (and
     (=> (mem1 y (tb2t (image int a r dom1)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom1) (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom1) (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r)))
     (mem1 y (tb2t (image int a r dom1))))) :pattern ((mem1
  y (tb2t (image int a r dom1)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int)))))
  (dom1 (set (set (tuple2 Int Int)))) (y (set (tuple2 Int Int))))
  (! (= (mem2 y
     (tb2t4
     (image (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 r)
     (t2tb4 dom1))))
     (exists ((x (set (tuple2 Int Int))))
     (and (mem2 x dom1) (mem
     (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
     (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
     (t2tb5 y)) (t2tb19 r))))) :pattern ((mem2
  y
  (tb2t4
  (image (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 r)
  (t2tb4 dom1))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 Int Int)) Int)))
  (dom1 (set (set (tuple2 Int Int)))) (y Int))
  (! (= (mem1 y
     (tb2t (image int (set1 (tuple21 int int)) (t2tb22 r) (t2tb4 dom1))))
     (exists ((x (set (tuple2 Int Int))))
     (and (mem2 x dom1) (mem (tuple21 (set1 (tuple21 int int)) int)
     (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y)) (t2tb22 r))))) :pattern ((mem1
  y (tb2t (image int (set1 (tuple21 int int)) (t2tb22 r) (t2tb4 dom1))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (set (tuple2 Int Int)))) (y uni))
  (! (= (mem b y (image b (set1 (tuple21 int int)) r (t2tb4 dom1)))
     (exists ((x (set (tuple2 Int Int))))
     (and (mem2 x dom1) (mem (tuple21 (set1 (tuple21 int int)) b)
     (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) r)))) :pattern ((mem
  b y (image b (set1 (tuple21 int int)) r (t2tb4 dom1)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int (set (tuple2 Int Int))))) (dom1 (set Int))
  (y (set (tuple2 Int Int))))
  (! (= (mem2 y
     (tb2t4 (image (set1 (tuple21 int int)) int (t2tb26 r) (t2tb dom1))))
     (exists ((x Int))
     (and (mem1 x dom1) (mem (tuple21 int (set1 (tuple21 int int)))
     (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y)) (t2tb26 r))))) :pattern ((mem2
  y (tb2t4 (image (set1 (tuple21 int int)) int (t2tb26 r) (t2tb dom1))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom1 (set Int)) (y Int))
  (! (= (mem1 y (tb2t (image int int (t2tb5 r) (t2tb dom1))))
     (exists ((x Int))
     (and (mem1 x dom1) (mem (tuple21 int int)
     (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 r))))) :pattern ((mem1
  y (tb2t (image int int (t2tb5 r) (t2tb dom1))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Int)) (y uni))
  (! (= (mem b y (image b int r (t2tb dom1)))
     (exists ((x Int))
     (and (mem1 x dom1) (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) r)))) :pattern ((mem
  b y (image b int r (t2tb dom1)))) ))))

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
  (forall ((f uni) (s uni) (t (set (set (tuple2 Int Int)))))
  (and
  (=> (mem (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t)))
  (and
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) f)
  (and (mem a x s) (mem2 y t))))
  (forall ((x uni) (y1 (set (tuple2 Int Int))) (y2 (set (tuple2 Int Int))))
  (=>
  (and (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y1)) f) (mem
  (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (forall ((x uni) (y1 (set (tuple2 Int Int))) (y2 (set (tuple2 Int Int))))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y1)) f) (mem
  (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (and
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f)
  (and (mem a x s) (mem1 y t))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb1 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb1 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int)))))
  (s (set (set (tuple2 Int Int)))) (t (set (set (tuple2 Int Int)))))
  (= (mem (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
  (t2tb19 f)
  (infix_plmngt (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 s)
  (t2tb4 t)))
  (and
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y)) (t2tb19 f)) (and (mem2 x s) (mem2 y t))))
  (forall ((x (set (tuple2 Int Int))) (y1 (set (tuple2 Int Int)))
  (y2 (set (tuple2 Int Int))))
  (=>
  (and (mem (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y1)) (t2tb19 f)) (mem
  (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y2)) (t2tb19 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 Int Int)) Int)))
  (s (set (set (tuple2 Int Int)))) (t (set Int)))
  (= (mem (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 f)
  (infix_plmngt int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t)))
  (and
  (forall ((x (set (tuple2 Int Int))) (y Int))
  (=> (mem (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y)) (t2tb22 f))
  (and (mem2 x s) (mem1 y t))))
  (forall ((x (set (tuple2 Int Int))) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y1)) (t2tb22 f)) (mem
  (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y2)) (t2tb22 f)))
  (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set (tuple2 Int Int)))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (and
  (forall ((x (set (tuple2 Int Int))) (y uni))
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) f)
  (and (mem2 x s) (mem b y t))))
  (forall ((x (set (tuple2 Int Int))) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y1) f) (mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x (set (tuple2 Int Int))) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (forall ((x (set (tuple2 Int Int))) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y1) f) (mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int (set (tuple2 Int Int))))) (s (set Int))
  (t (set (set (tuple2 Int Int)))))
  (= (mem (set1 (tuple21 int (set1 (tuple21 int int)))) (t2tb26 f)
  (infix_plmngt (set1 (tuple21 int int)) int (t2tb s) (t2tb4 t)))
  (and
  (forall ((x Int) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y)) (t2tb26 f))
  (and (mem1 x s) (mem2 y t))))
  (forall ((x Int) (y1 (set (tuple2 Int Int))) (y2 (set (tuple2 Int Int))))
  (=>
  (and (mem (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y1)) (t2tb26 f)) (mem
  (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y2)) (t2tb26 f)))
  (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (and
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 f))
  (and (mem1 x s) (mem1 y t))))
  (forall ((x Int) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y1))
  (t2tb5 f)) (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y2))
  (t2tb5 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t))
  (and
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) f)
  (and (mem1 x s) (mem b y t))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb1 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb1 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t)))))))

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
  (forall ((f uni) (s (set (set (tuple2 Int Int)))) (t uni)
  (x (set (tuple2 Int Int))) (y uni))
  (=> (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) f) (mem2 x s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)) (x Int)
  (y Int))
  (=> (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 f))
  (mem1 x s)))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (x Int) (y uni))
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) f) (mem1 x s))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set (tuple2 Int Int)))) (x uni)
  (y (set (tuple2 Int Int))))
  (=> (mem (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t)))
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) f) (mem2 y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (x uni) (y Int))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f) (mem1 y t))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)) (x Int)
  (y Int))
  (=> (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 f))
  (mem1 y t)))))

;; range_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem b y t))))))

;; function_extend_range
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int))
  (u (set Int)))
  (=> (subset int (t2tb t) (t2tb u))
  (=> (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2 f
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb u))))))))

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
  (forall ((f uni) (s uni) (t (set (set (tuple2 Int Int))))
  (u (set (set (tuple2 Int Int)))))
  (=> (subset (set1 (tuple21 int int)) (t2tb4 u) (t2tb4 t))
  (=> (mem (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t)))
  (=>
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) f) (mem2 y u)))) (mem
  (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (u (set Int)))
  (=> (subset int (t2tb u) (t2tb t))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb u)))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int))
  (u (set Int)))
  (=> (subset int (t2tb u) (t2tb t))
  (=> (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (=>
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 f))
  (mem1 y u))) (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb u)))))))))

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
  (forall ((x (set (tuple2 Int Int))))
  (and
  (=> (mem2 x (tb2t4 (dom b (set1 (tuple21 int int)) r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) r)) (mem2 x
  (tb2t4 (dom b (set1 (tuple21 int int)) r)))))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x Int))
  (and
  (=> (mem1 x (tb2t (dom b int r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) r))))
  (=> (exists ((y uni)) (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) r))
  (mem1 x (tb2t (dom b int r)))))))))

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
  (forall ((y (set (tuple2 Int Int))))
  (and
  (=> (mem2 y (tb2t4 (ran (set1 (tuple21 int int)) a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) r)) (mem2 y
  (tb2t4 (ran (set1 (tuple21 int int)) a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y Int))
  (and
  (=> (mem1 y (tb2t (ran int a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r))))
  (=> (exists ((x uni)) (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r))
  (mem1 y (tb2t (ran int a r)))))))))

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
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (= (tb2t (dom int int (t2tb5 f))) s)))))

;; mem_total_functions
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 a) s)
  (= (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (= (dom b a f) s)))))))

;; total_function_is_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=> (mem2 f (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t)))) (mem2 f
     (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))) :pattern ((mem2
  f (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t))))) )))

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
  (forall ((s uni) (t (set (set (tuple2 Int Int)))) (x uni)
  (y (set (tuple2 Int Int))))
  (=> (and (mem a x s) (mem2 y t)) (mem
  (set1 (tuple21 a (set1 (tuple21 int int))))
  (add (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y))
  (empty (tuple21 a (set1 (tuple21 int int)))))
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set Int)) (x uni) (y Int))
  (=> (and (mem a x s) (mem1 y t)) (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 Int Int)))) (t (set (set (tuple2 Int Int))))
  (x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (=> (and (mem2 x s) (mem2 y t)) (mem
  (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
  (add (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y))
  (empty (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))))
  (infix_plmngt (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 s)
  (t2tb4 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 Int Int)))) (t (set Int)) (x (set (tuple2 Int
  Int))) (y Int))
  (=> (and (mem2 x s) (mem1 y t)) (mem
  (set1 (tuple21 (set1 (tuple21 int int)) int))
  (add (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y))
  (empty (tuple21 (set1 (tuple21 int int)) int)))
  (infix_plmngt int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (set (tuple2 Int Int)))) (t uni) (x (set (tuple2 Int
  Int))) (y uni))
  (=> (and (mem2 x s) (mem b y t)) (mem
  (set1 (tuple21 (set1 (tuple21 int int)) b))
  (add (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y)
  (empty (tuple21 (set1 (tuple21 int int)) b)))
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set (set (tuple2 Int Int)))) (x Int)
  (y (set (tuple2 Int Int))))
  (=> (and (mem1 x s) (mem2 y t)) (mem
  (set1 (tuple21 int (set1 (tuple21 int int))))
  (add (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y))
  (empty (tuple21 int (set1 (tuple21 int int)))))
  (infix_plmngt (set1 (tuple21 int int)) int (t2tb s) (t2tb4 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem2
  (tb2t5
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
  (empty (tuple21 int int))))
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (x Int) (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (empty (tuple21 int b)))
  (infix_plmngt b int (t2tb s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (x uni) (y uni))
  (=> (and (mem a x s) (mem b y t)) (mem (set1 (tuple21 a b))
  (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b)))
  (infix_plmngt b a s t))))))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem2
  (tb2t5
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
  (empty (tuple21 int int))))
  (tb2t4
  (infix_mnmngt int int (add int (t2tb1 x) (empty int))
  (add int (t2tb1 y) (empty int))))) :pattern ((tb2t5
                                               (add (tuple21 int int)
                                               (Tuple2 int int (t2tb1 x)
                                               (t2tb1 y))
                                               (empty (tuple21 int int))))) )))

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
  (forall ((f uni) (s (set (set (tuple2 Int Int)))) (t uni)
  (a (set (tuple2 Int Int))))
  (=>
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)) (mem2 a
  (tb2t4 (dom b (set1 (tuple21 int int)) f)))) (mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 a)
  (apply b (set1 (tuple21 int int)) f (t2tb5 a))) f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)) (a Int))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem1 a
  (tb2t (dom int int (t2tb5 f))))) (mem (tuple21 int int)
  (Tuple2 int int (t2tb1 a) (apply int int (t2tb5 f) (t2tb1 a))) (t2tb5 f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t)) (mem1 a
  (tb2t (dom b int f)))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb1 a) (apply b int f (t2tb1 a))) f)))))

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
  (forall ((f uni) (s (set (set (tuple2 Int Int)))) (t uni)
  (a (set (tuple2 Int Int))))
  (=>
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_mnmngt b (set1 (tuple21 int int)) (t2tb4 s) t)) (mem2 a s)) (mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 a)
  (apply b (set1 (tuple21 int int)) f (t2tb5 a))) f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)) (a Int))
  (=>
  (and (mem2 f (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t)))) (mem1 a s))
  (mem (tuple21 int int)
  (Tuple2 int int (t2tb1 a) (apply int int (t2tb5 f) (t2tb1 a))) (t2tb5 f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_mnmngt b int (t2tb s) t)) (mem1 a
  s)) (mem (tuple21 int b) (Tuple2 int b (t2tb1 a) (apply b int f (t2tb1 a)))
  f)))))

;; apply_def1
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=> (and (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem a a1 s))
  (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)) (a Int)
  (b Int))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem
  (tuple21 int int) (Tuple2 int int (t2tb1 a) (t2tb1 b)) (t2tb5 f)))
  (= (tb2t1 (apply int int (t2tb5 f) (t2tb1 a))) b))))

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
  (forall ((x uni) (f uni) (s uni) (t (set (set (tuple2 Int Int)))))
  (! (=>
     (and (mem (set1 (tuple21 a (set1 (tuple21 int int)))) f
     (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t))) (mem a x
     (dom (set1 (tuple21 int int)) a f))) (mem2
     (tb2t5 (apply (set1 (tuple21 int int)) a f x)) t)) :pattern ((mem
  (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t)))
  (tb2t5 (apply (set1 (tuple21 int int)) a f x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t))) (mem
     a x (dom int a f))) (mem1 (tb2t1 (apply int a f x)) t)) :pattern ((mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (tb2t1 (apply int a f x))) ))))

;; apply_range
  (assert
  (forall ((x (set (tuple2 Int Int))) (f (set (tuple2 (set (tuple2 Int Int))
  (set (tuple2 Int Int))))) (s (set (set (tuple2 Int Int))))
  (t (set (set (tuple2 Int Int)))))
  (! (=>
     (and (mem
     (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
     (t2tb19 f)
     (infix_plmngt (set1 (tuple21 int int)) (set1 (tuple21 int int))
     (t2tb4 s) (t2tb4 t))) (mem2 x
     (tb2t4
     (dom (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 f)))))
     (mem2
     (tb2t5
     (apply (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 f)
     (t2tb5 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
  (t2tb19 f)
  (infix_plmngt (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 s)
  (t2tb4 t)))
  (tb2t5
  (apply (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 f)
  (t2tb5 x)))) )))

;; apply_range
  (assert
  (forall ((x (set (tuple2 Int Int))) (f (set (tuple2 (set (tuple2 Int Int))
  Int))) (s (set (set (tuple2 Int Int)))) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 f)
     (infix_plmngt int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t))) (mem2 x
     (tb2t4 (dom int (set1 (tuple21 int int)) (t2tb22 f))))) (mem1
     (tb2t1 (apply int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 f)
  (infix_plmngt int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t)))
  (tb2t1 (apply int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 Int Int))) (f uni) (s (set (set (tuple2 Int
  Int)))) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
     (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)) (mem2 x
     (tb2t4 (dom b (set1 (tuple21 int int)) f)))) (mem b
     (apply b (set1 (tuple21 int int)) f (t2tb5 x)) t)) :pattern ((mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (apply b (set1 (tuple21 int int)) f (t2tb5 x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int (set (tuple2 Int Int)))))
  (s (set Int)) (t (set (set (tuple2 Int Int)))))
  (! (=>
     (and (mem (set1 (tuple21 int (set1 (tuple21 int int)))) (t2tb26 f)
     (infix_plmngt (set1 (tuple21 int int)) int (t2tb s) (t2tb4 t))) (mem1 x
     (tb2t (dom (set1 (tuple21 int int)) int (t2tb26 f))))) (mem2
     (tb2t5 (apply (set1 (tuple21 int int)) int (t2tb26 f) (t2tb1 x))) t)) :pattern ((mem
  (set1 (tuple21 int (set1 (tuple21 int int)))) (t2tb26 f)
  (infix_plmngt (set1 (tuple21 int int)) int (t2tb s) (t2tb4 t)))
  (tb2t5 (apply (set1 (tuple21 int int)) int (t2tb26 f) (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=>
     (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem1 x
     (tb2t (dom int int (t2tb5 f))))) (mem1
     (tb2t1 (apply int int (t2tb5 f) (t2tb1 x))) t)) :pattern ((mem2
  f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (tb2t1 (apply int int (t2tb5 f) (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x Int) (f uni) (s (set Int)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t))
     (mem1 x (tb2t (dom b int f)))) (mem b (apply b int f (t2tb1 x)) t)) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t))
  (apply b int f (t2tb1 x))) ))))

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
  (forall ((a ty))
  (forall ((f uni) (g (set (tuple2 Int Int))) (s uni) (t (set Int))
  (u (set Int)))
  (=>
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t))) (mem2 g
  (tb2t4 (infix_plmngt int int (t2tb t) (t2tb u))))) (mem
  (set1 (tuple21 a int)) (semicolon int int a f (t2tb5 g))
  (infix_plmngt int a s (t2tb u)))))))

;; semicolon_is_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni) (s (set Int)) (t uni) (u (set Int)))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t)) (mem
  (set1 (tuple21 b int)) g (infix_plmngt int b t (t2tb u)))) (mem2
  (tb2t5 (semicolon int b int f g))
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb u))))))))

;; semicolon_is_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (g (set (tuple2 Int Int)))
  (s (set Int)) (t (set Int)) (u (set Int)))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2 g
  (tb2t4 (infix_plmngt int int (t2tb t) (t2tb u))))) (mem2
  (tb2t5 (semicolon int int int (t2tb5 f) (t2tb5 g)))
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb u)))))))

;; semicolon_is_function
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 Int Int))) (g uni) (s (set Int)) (t (set Int))
  (u uni))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem
  (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb t) u))) (mem
  (set1 (tuple21 int c)) (semicolon c int int (t2tb5 f) g)
  (infix_plmngt c int (t2tb s) u))))))

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
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set (set (tuple2 Int Int))))
  (u uni))
  (=>
  (and (mem (set1 (tuple21 a (set1 (tuple21 int int)))) f
  (infix_plmngt (set1 (tuple21 int int)) a s (t2tb4 t)))
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) c)) g
  (infix_plmngt c (set1 (tuple21 int int)) (t2tb4 t) u))
  (and (mem a x (dom (set1 (tuple21 int int)) a f)) (mem2
  (tb2t5 (apply (set1 (tuple21 int int)) a f x))
  (tb2t4 (dom c (set1 (tuple21 int int)) g))))))
  (= (apply c a (semicolon c (set1 (tuple21 int int)) a f g) x) (apply c
                                                                (set1
                                                                (tuple21 
                                                                int int)) g
                                                                (apply
                                                                (set1
                                                                (tuple21 
                                                                int int)) a f
                                                                x)))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 Int Int))) (s uni) (t (set Int))
  (u (set Int)))
  (=>
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (and (mem2 g (tb2t4 (infix_plmngt int int (t2tb t) (t2tb u))))
  (and (mem a x (dom int a f)) (mem1 (tb2t1 (apply int a f x))
  (tb2t (dom int int (t2tb5 g)))))))
  (= (tb2t1 (apply int a (semicolon int int a f (t2tb5 g)) x)) (tb2t1
                                                               (apply 
                                                               int int
                                                               (t2tb5 g)
                                                               (apply 
                                                               int a f x))))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb t) u))
  (and (mem a x (dom int a f)) (mem1 (tb2t1 (apply int a f x))
  (tb2t (dom c int g))))))
  (= (apply c a (semicolon c int a f g) x) (apply c int g (apply int a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 Int Int))) (f (set (tuple2 (set (tuple2 Int Int))
  (set (tuple2 Int Int))))) (g uni) (s (set (set (tuple2 Int Int))))
  (t (set (set (tuple2 Int Int)))) (u uni))
  (=>
  (and (mem
  (set1 (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int))))
  (t2tb19 f)
  (infix_plmngt (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 s)
  (t2tb4 t)))
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) c)) g
  (infix_plmngt c (set1 (tuple21 int int)) (t2tb4 t) u))
  (and (mem2 x
  (tb2t4 (dom (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 f))))
  (mem2
  (tb2t5
  (apply (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb19 f)
  (t2tb5 x))) (tb2t4 (dom c (set1 (tuple21 int int)) g))))))
  (= (apply c (set1 (tuple21 int int))
     (semicolon c (set1 (tuple21 int int)) (set1 (tuple21 int int))
     (t2tb19 f) g) (t2tb5 x)) (apply c (set1 (tuple21 int int)) g
                              (apply (set1 (tuple21 int int))
                              (set1 (tuple21 int int)) (t2tb19 f) (t2tb5 x))))))))

;; apply_compose
  (assert
  (forall ((x (set (tuple2 Int Int))) (f (set (tuple2 (set (tuple2 Int Int))
  Int))) (g (set (tuple2 Int Int))) (s (set (set (tuple2 Int Int))))
  (t (set Int)) (u (set Int)))
  (=>
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 f)
  (infix_plmngt int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t)))
  (and (mem2 g (tb2t4 (infix_plmngt int int (t2tb t) (t2tb u))))
  (and (mem2 x (tb2t4 (dom int (set1 (tuple21 int int)) (t2tb22 f)))) (mem1
  (tb2t1 (apply int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 x)))
  (tb2t (dom int int (t2tb5 g)))))))
  (= (tb2t1
     (apply int (set1 (tuple21 int int))
     (semicolon int int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 g))
     (t2tb5 x))) (tb2t1
                 (apply int int (t2tb5 g)
                 (apply int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 Int Int))) (f (set (tuple2 (set (tuple2 Int Int))
  Int))) (g uni) (s (set (set (tuple2 Int Int)))) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) int)) (t2tb22 f)
  (infix_plmngt int (set1 (tuple21 int int)) (t2tb4 s) (t2tb t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb t) u))
  (and (mem2 x (tb2t4 (dom int (set1 (tuple21 int int)) (t2tb22 f)))) (mem1
  (tb2t1 (apply int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 x)))
  (tb2t (dom c int g))))))
  (= (apply c (set1 (tuple21 int int))
     (semicolon c int (set1 (tuple21 int int)) (t2tb22 f) g) (t2tb5 x)) 
  (apply c int g (apply int (set1 (tuple21 int int)) (t2tb22 f) (t2tb5 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (set (tuple2 Int Int))) (f uni) (g uni)
  (s (set (set (tuple2 Int Int)))) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem2 x (tb2t4 (dom b (set1 (tuple21 int int)) f))) (mem b
  (apply b (set1 (tuple21 int int)) f (t2tb5 x)) (dom c b g)))))
  (= (apply c (set1 (tuple21 int int))
     (semicolon c b (set1 (tuple21 int int)) f g) (t2tb5 x)) (apply c b g
                                                             (apply b
                                                             (set1
                                                             (tuple21 
                                                             int int)) f
                                                             (t2tb5 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int (set (tuple2 Int Int))))) (g uni)
  (s (set Int)) (t (set (set (tuple2 Int Int)))) (u uni))
  (=>
  (and (mem (set1 (tuple21 int (set1 (tuple21 int int)))) (t2tb26 f)
  (infix_plmngt (set1 (tuple21 int int)) int (t2tb s) (t2tb4 t)))
  (and (mem (set1 (tuple21 (set1 (tuple21 int int)) c)) g
  (infix_plmngt c (set1 (tuple21 int int)) (t2tb4 t) u))
  (and (mem1 x (tb2t (dom (set1 (tuple21 int int)) int (t2tb26 f)))) (mem2
  (tb2t5 (apply (set1 (tuple21 int int)) int (t2tb26 f) (t2tb1 x)))
  (tb2t4 (dom c (set1 (tuple21 int int)) g))))))
  (= (apply c int (semicolon c (set1 (tuple21 int int)) int (t2tb26 f) g)
     (t2tb1 x)) (apply c (set1 (tuple21 int int)) g
                (apply (set1 (tuple21 int int)) int (t2tb26 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (g (set (tuple2 Int Int)))
  (s (set Int)) (t (set Int)) (u (set Int)))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (and (mem2 g (tb2t4 (infix_plmngt int int (t2tb t) (t2tb u))))
  (and (mem1 x (tb2t (dom int int (t2tb5 f)))) (mem1
  (tb2t1 (apply int int (t2tb5 f) (t2tb1 x)))
  (tb2t (dom int int (t2tb5 g)))))))
  (= (tb2t1
     (apply int int (semicolon int int int (t2tb5 f) (t2tb5 g)) (t2tb1 x))) 
  (tb2t1 (apply int int (t2tb5 g) (apply int int (t2tb5 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int Int))) (g uni) (s (set Int))
  (t (set Int)) (u uni))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb t) u))
  (and (mem1 x (tb2t (dom int int (t2tb5 f)))) (mem1
  (tb2t1 (apply int int (t2tb5 f) (t2tb1 x))) (tb2t (dom c int g))))))
  (= (apply c int (semicolon c int int (t2tb5 f) g) (t2tb1 x)) (apply c 
                                                               int g
                                                               (apply 
                                                               int int
                                                               (t2tb5 f)
                                                               (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x Int) (f uni) (g uni) (s (set Int)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t (dom b int f))) (mem b (apply b int f (t2tb1 x))
  (dom c b g)))))
  (= (apply c int (semicolon c b int f g) (t2tb1 x)) (apply c b g
                                                     (apply b int f
                                                     (t2tb1 x))))))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_gtplgt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2
  (tb2t5 (inverse int int (t2tb5 f)))
  (tb2t4 (infix_plmngt int int (t2tb t) (t2tb s))))))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_gtmngt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_gtplgt int int (t2tb s) (t2tb t)))) (mem2 f
  (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t))))))))

;; mem_total_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_mnmngt b a s t)))))))

;; mem_total_injection_alt
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_gtmngt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t)))) (mem2
  (tb2t5 (inverse int int (t2tb5 f)))
  (tb2t4 (infix_plmngt int int (t2tb t) (t2tb s))))))))

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
  (forall ((f uni) (s (set (set (tuple2 Int Int)))) (t uni))
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (=> (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_gtmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (=> (mem2 x s)
  (=> (mem2 y s)
  (=>
  (= (apply b (set1 (tuple21 int int)) f (t2tb5 x)) (apply b
                                                    (set1 (tuple21 int int))
                                                    f (t2tb5 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (forall ((x Int) (y Int))
  (=> (mem2 f (tb2t4 (infix_gtmngt int int (t2tb s) (t2tb t))))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=>
  (= (tb2t1 (apply int int (t2tb5 f) (t2tb1 x))) (tb2t1
                                                 (apply int int (t2tb5 f)
                                                 (t2tb1 y))))
  (= x y))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (forall ((x Int) (y Int))
  (=> (mem (set1 (tuple21 int b)) f (infix_gtmngt b int (t2tb s) t))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=> (= (apply b int f (t2tb1 x)) (apply b int f (t2tb1 y))) (= x y)))))))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_plmngtgt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (= (tb2t (ran int int (t2tb5 f))) t)))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_mnmngtgt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_plmngtgt int int (t2tb s) (t2tb t)))) (mem2 f
  (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb t))))))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_gtplgtgt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_gtplgt int int (t2tb s) (t2tb t)))) (mem2 f
  (tb2t4 (infix_plmngtgt int int (t2tb s) (t2tb t))))))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem2 f (tb2t4 (infix_gtmngtgt int int (t2tb s) (t2tb t))))
  (and (mem2 f (tb2t4 (infix_gtmngt int int (t2tb s) (t2tb t)))) (mem2 f
  (tb2t4 (infix_mnmngtgt int int (t2tb s) (t2tb t))))))))

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

(declare-fun id1 ((set Int)) (set (tuple2 Int Int)))

;; id_def
  (assert
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int)))
  (s (set (set (tuple2 Int Int)))))
  (= (mem (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y)) (id (set1 (tuple21 int int)) (t2tb4 s)))
  (and (mem2 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
  (t2tb5 (id1 s))) (and (mem1 x s) (= x y)))))

;; id_def
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni) (s uni))
  (=> (sort a x)
  (=> (sort a y)
  (= (mem (tuple21 a a) (Tuple2 a a x y) (id a s)) (and (mem a x s) (= x y))))))))

;; id_dom
  (assert
  (forall ((s (set Int))) (= (tb2t (dom int int (t2tb5 (id1 s)))) s)))

;; id_dom
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (sort (set1 a) s) (= (dom a a (id a s)) s)))))

;; id_ran
  (assert
  (forall ((s (set Int))) (= (tb2t (ran int int (t2tb5 (id1 s)))) s)))

;; id_ran
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (sort (set1 a) s) (= (ran a a (id a s)) s)))))

;; id_fun
  (assert
  (forall ((s (set Int))) (mem2 (id1 s)
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb s))))))

;; id_fun
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 (tuple21 a a)) (id a s)
  (infix_plmngt a a s s)))))

;; id_total_fun
  (assert
  (forall ((s (set Int))) (mem2 (id1 s)
  (tb2t4 (infix_mnmngt int int (t2tb s) (t2tb s))))))

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
  (forall ((n1 Int) (n2 Int) (s1 (set Int)) (s2 (set Int))
  (r (set (tuple2 Int Int))))
  (=> (and (<= 0 n1) (mem2 r (tb2t4 (seq_length int n1 (t2tb s1)))))
  (=> (and (<= 0 n2) (mem2 r (tb2t4 (seq_length int n2 (t2tb s2)))))
  (= n1 n2)))))

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
  (forall ((n Int) (s (set Int)) (r (set (tuple2 Int Int))))
  (=> (and (<= 0 n) (mem2 r (tb2t4 (seq_length int n (t2tb s)))))
  (= (size int (t2tb5 r)) n))))

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

(declare-fun seq2 ((set Int)) (set (set (tuple2 Int Int))))

;; seq_def
  (assert
  (forall ((s (set Int)) (r (set (tuple2 Int Int))))
  (= (mem2 r (seq2 s))
  (and (<= 0 (size int (t2tb5 r))) (mem2 r
  (tb2t4 (seq_length int (size int (t2tb5 r)) (t2tb s))))))))

;; seq_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (r uni))
  (= (mem (set1 (tuple21 int a)) r (seq a s))
  (and (<= 0 (size a r)) (mem (set1 (tuple21 int a)) r
  (seq_length a (size a r) s)))))))

;; seq_as_total_function
  (assert
  (forall ((s (set Int)) (r (set (tuple2 Int Int))))
  (=> (mem2 r (seq2 s)) (mem2 r
  (tb2t4 (infix_mnmngt int int (t2tb (mk 1 (size int (t2tb5 r)))) (t2tb s)))))))

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
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))) (c Int))
  (=> (is_finite_subset (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2) c)
  (=> (mem2 x s2)
  (=> (mem2 x s1) (is_finite_subset (set1 (tuple21 int int))
  (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1)) (t2tb4 s2) c))))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset int (add int (t2tb1 x) (t2tb s1))
  (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))) (c Int))
  (=> (is_finite_subset (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2) c)
  (=> (mem2 x s2)
  (=> (not (mem2 x s1)) (is_finite_subset (set1 (tuple21 int int))
  (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1)) (t2tb4 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset int (add int (t2tb1 x) (t2tb s1))
  (t2tb s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2)
  (=> (not (mem a x s1)) (is_finite_subset a (add a x s1) s2 (+ c 1))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (set (tuple2 Int Int)))) (z1 (set (set (tuple2 Int Int))))
  (z2 Int))
  (=> (is_finite_subset (set1 (tuple21 int int)) (t2tb4 z) (t2tb4 z1) z2)
  (or
  (or
  (exists ((s (set (set (tuple2 Int Int)))))
  (and (and (= z (tb2t4 (empty (set1 (tuple21 int int))))) (= z1 s))
  (= z2 0)))
  (exists ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))) (c Int))
  (and (is_finite_subset (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2) c)
  (and (mem2 x s2)
  (and (mem2 x s1)
  (and
  (and (= z (tb2t4 (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))) (c Int))
  (and (is_finite_subset (set1 (tuple21 int int)) (t2tb4 s1) (t2tb4 s2) c)
  (and (mem2 x s2)
  (and (not (mem2 x s1))
  (and
  (and (= z (tb2t4 (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb z) (t2tb z1) z2)
  (or
  (or
  (exists ((s (set Int)))
  (and (and (= z (tb2t (empty int))) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1)
  (and (and (= z (tb2t (add int (t2tb1 x) (t2tb s1)))) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (and (mem1 x s2)
  (and (not (mem1 x s1))
  (and (and (= z (tb2t (add int (t2tb1 x) (t2tb s1)))) (= z1 s2))
  (= z2 (+ c 1)))))))))))

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
  (forall ((s (set (tuple2 Int Int))) (x (set (tuple2 Int Int))))
  (= (mem2 x (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s))))
  (exists ((c Int)) (is_finite_subset (tuple21 int int) (t2tb5 x) (t2tb5 s)
  c)))))

;; finite_subsets_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 Int Int)))) (mem2
  (tb2t5 (empty (tuple21 int int)))
  (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s))))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

(declare-fun t2tb27 ((set (set (set (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set (tuple2 Int Int)))))) (sort
  (set1 (set1 (set1 (tuple21 int int)))) (t2tb27 x))))

(declare-fun tb2t27 (uni) (set (set (set (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (set (tuple2 Int Int))))))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb27 (tb2t27 j)) j) :pattern ((t2tb27 (tb2t27 j))) )))

;; finite_Add
  (assert
  (forall ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))))
  (=> (mem (set1 (set1 (tuple21 int int))) (t2tb4 s1)
  (finite_subsets (set1 (tuple21 int int)) (t2tb4 s2)))
  (=> (mem2 x s2) (mem (set1 (set1 (tuple21 int int)))
  (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1))
  (finite_subsets (set1 (tuple21 int int)) (t2tb4 s2)))))))

;; finite_Add
  (assert
  (forall ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))))
  (=> (mem2 s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))
  (=> (mem (tuple21 int int) (t2tb6 x) (t2tb5 s2)) (mem2
  (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))
  (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))))))

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

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (=> (mem1 x s2) (mem (set1 int) (add int (t2tb1 x) (t2tb s1))
  (finite_subsets int (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int)))
  (s3 (set (tuple2 Int Int))))
  (=> (mem2 s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3))))
  (=> (mem2 s2 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3)))) (mem2
  (tb2t5 (union (tuple21 int int) (t2tb5 s1) (t2tb5 s2)))
  (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3))))))))

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
  (=> (mem2 s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))
  (or (= s1 (tb2t5 (empty (tuple21 int int))))
  (exists ((x (tuple2 Int Int)) (s3 (set (tuple2 Int Int))))
  (and (= s1 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s3)))) (mem2 s3
  (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))))))))

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
  (= (mem2 x (tb2t4 (non_empty_finite_subsets (tuple21 int int) (t2tb5 s))))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb5 x) (t2tb5 s) c)
  (not (= x (tb2t5 (empty (tuple21 int int))))))))))

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
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))))
  (! (=> (mem (set1 (set1 (tuple21 int int))) (t2tb4 s1)
     (finite_subsets (set1 (tuple21 int int)) (t2tb4 s2)))
     (=> (not (mem2 x s1))
     (= (card (set1 (tuple21 int int))
        (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1))) (+ (card
                                                                (set1
                                                                (tuple21 
                                                                int int))
                                                                (t2tb4 s1)) 1)))) :pattern ((mem
  (set1 (set1 (tuple21 int int))) (t2tb4 s1)
  (finite_subsets (set1 (tuple21 int int)) (t2tb4 s2)))
  (card (set1 (tuple21 int int))
  (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))))
  (! (=> (mem2 s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))
     (=> (not (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1)))
     (= (card (tuple21 int int) (add (tuple21 int int) (t2tb6 x) (t2tb5 s1))) (+ 
     (card (tuple21 int int) (t2tb5 s1)) 1)))) :pattern ((mem2
  s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))
  (card (tuple21 int int) (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
     (=> (not (mem1 x s1))
     (= (card int (add int (t2tb1 x) (t2tb s1))) (+ (card int (t2tb s1)) 1)))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (card int (add int (t2tb1 x) (t2tb s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (set (tuple2 Int Int))) (s1 (set (set (tuple2 Int Int))))
  (s2 (set (set (tuple2 Int Int)))))
  (! (=> (mem (set1 (set1 (tuple21 int int))) (t2tb4 s1)
     (finite_subsets (set1 (tuple21 int int)) (t2tb4 s2)))
     (=> (mem2 x s1)
     (= (card (set1 (tuple21 int int))
        (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1))) (card
                                                             (set1
                                                             (tuple21 
                                                             int int))
                                                             (t2tb4 s1))))) :pattern ((mem
  (set1 (set1 (tuple21 int int))) (t2tb4 s1)
  (finite_subsets (set1 (tuple21 int int)) (t2tb4 s2)))
  (card (set1 (tuple21 int int))
  (add (set1 (tuple21 int int)) (t2tb5 x) (t2tb4 s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))))
  (! (=> (mem2 s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))
     (=> (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1))
     (= (card (tuple21 int int) (add (tuple21 int int) (t2tb6 x) (t2tb5 s1))) 
     (card (tuple21 int int) (t2tb5 s1))))) :pattern ((mem2
  s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s2))))
  (card (tuple21 int int) (add (tuple21 int int) (t2tb6 x) (t2tb5 s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
     (=> (mem1 x s1)
     (= (card int (add int (t2tb1 x) (t2tb s1))) (card int (t2tb s1))))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (card int (add int (t2tb1 x) (t2tb s1)))) )))

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
  (! (=> (mem2 s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3))))
     (=> (mem2 s2 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3))))
     (=> (is_empty (tuple21 int int)
     (inter (tuple21 int int) (t2tb5 s1) (t2tb5 s2)))
     (= (card (tuple21 int int)
        (union (tuple21 int int) (t2tb5 s1) (t2tb5 s2))) (+ (card
                                                            (tuple21 int int)
                                                            (t2tb5 s1)) 
     (card (tuple21 int int) (t2tb5 s2))))))) :pattern ((mem2
  s1 (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3)))) (mem2 s2
  (tb2t4 (finite_subsets (tuple21 int int) (t2tb5 s3))))
  (card (tuple21 int int) (union (tuple21 int int) (t2tb5 s1) (t2tb5 s2)))) )))

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
  (forall ((a1 uni) (b (set (set (tuple2 Int Int)))) (x uni)
  (y (set (tuple2 Int Int))))
  (! (= (mem (tuple21 a (set1 (tuple21 int int)))
     (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y))
     (times (set1 (tuple21 int int)) a a1 (t2tb4 b)))
     (and (mem a x a1) (mem2 y b))) :pattern ((mem
  (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y))
  (times (set1 (tuple21 int int)) a a1 (t2tb4 b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set Int)) (x uni) (y Int))
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y))
     (times int a a1 (t2tb b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (times int a a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 Int Int)))) (b (set (set (tuple2 Int Int))))
  (x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (! (= (mem (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
     (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
     (t2tb5 y))
     (times (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 a)
     (t2tb4 b))) (and (mem2 x a) (mem2 y b))) :pattern ((mem
  (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y))
  (times (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 a)
  (t2tb4 b)))) )))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 Int Int)))) (b (set Int)) (x (set (tuple2 Int
  Int))) (y Int))
  (! (= (mem (tuple21 (set1 (tuple21 int int)) int)
     (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y))
     (times int (set1 (tuple21 int int)) (t2tb4 a) (t2tb b)))
     (and (mem2 x a) (mem1 y b))) :pattern ((mem
  (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y))
  (times int (set1 (tuple21 int int)) (t2tb4 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (set (tuple2 Int Int)))) (b1 uni) (x (set (tuple2 Int
  Int))) (y uni))
  (! (= (mem (tuple21 (set1 (tuple21 int int)) b)
     (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y)
     (times b (set1 (tuple21 int int)) (t2tb4 a) b1))
     (and (mem2 x a) (mem b y b1))) :pattern ((mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y)
  (times b (set1 (tuple21 int int)) (t2tb4 a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set (set (tuple2 Int Int)))) (x Int)
  (y (set (tuple2 Int Int))))
  (! (= (mem (tuple21 int (set1 (tuple21 int int)))
     (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y))
     (times (set1 (tuple21 int int)) int (t2tb a) (t2tb4 b)))
     (and (mem1 x a) (mem2 y b))) :pattern ((mem
  (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y))
  (times (set1 (tuple21 int int)) int (t2tb a) (t2tb4 b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set Int)) (x Int) (y Int))
  (! (= (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
     (times int int (t2tb a) (t2tb b))) (and (mem1 x a) (mem1 y b))) :pattern ((mem
  (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
  (times int int (t2tb a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set Int)) (b1 uni) (x Int) (y uni))
  (! (= (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y)
     (times b int (t2tb a) b1)) (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (times b int (t2tb a) b1))) ))))

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
  (forall ((r (set (tuple2 Int Int))) (u (set Int)) (v (set Int)))
  (= (mem2 r
  (tb2t4 (power1 (tuple21 int int) (times int int (t2tb u) (t2tb v)))))
  (subset (tuple21 int int) (t2tb5 r) (times int int (t2tb u) (t2tb v))))))

;; break_power_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (= (mem (set1 (tuple21 a b)) r (power1 (tuple21 a b) (times b a u v)))
  (subset (tuple21 a b) r (times b a u v))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set (set (tuple2 Int Int)))))
  (and
  (=> (subset (tuple21 a (set1 (tuple21 int int))) r
  (times (set1 (tuple21 int int)) a u (t2tb4 v)))
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) r)
  (and (mem a x u) (mem2 y v)))))
  (=>
  (forall ((x uni) (y (set (tuple2 Int Int))))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 (tuple21 int int)))
  (Tuple2 a (set1 (tuple21 int int)) x (t2tb5 y)) r)
  (and (mem a x u) (mem2 y v))))) (subset
  (tuple21 a (set1 (tuple21 int int))) r
  (times (set1 (tuple21 int int)) a u (t2tb4 v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set Int)))
  (and
  (=> (subset (tuple21 a int) r (times int a u (t2tb v)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r)
  (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r)
  (and (mem a x u) (mem1 y v))))) (subset (tuple21 a int) r
  (times int a u (t2tb v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 Int Int)) (set (tuple2 Int Int)))))
  (u (set (set (tuple2 Int Int)))) (v (set (set (tuple2 Int Int)))))
  (= (subset (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (t2tb19 r)
  (times (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb4 u)
  (t2tb4 v)))
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 (set1 (tuple21 int int)) (set1 (tuple21 int int)))
  (Tuple2 (set1 (tuple21 int int)) (set1 (tuple21 int int)) (t2tb5 x)
  (t2tb5 y)) (t2tb19 r)) (and (mem2 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 Int Int)) Int)))
  (u (set (set (tuple2 Int Int)))) (v (set Int)))
  (= (subset (tuple21 (set1 (tuple21 int int)) int) (t2tb22 r)
  (times int (set1 (tuple21 int int)) (t2tb4 u) (t2tb v)))
  (forall ((x (set (tuple2 Int Int))) (y Int))
  (=> (mem (tuple21 (set1 (tuple21 int int)) int)
  (Tuple2 (set1 (tuple21 int int)) int (t2tb5 x) (t2tb1 y)) (t2tb22 r))
  (and (mem2 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (set (tuple2 Int Int)))) (v uni))
  (and
  (=> (subset (tuple21 (set1 (tuple21 int int)) b) r
  (times b (set1 (tuple21 int int)) (t2tb4 u) v))
  (forall ((x (set (tuple2 Int Int))) (y uni))
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) r)
  (and (mem2 x u) (mem b y v)))))
  (=>
  (forall ((x (set (tuple2 Int Int))) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) r)
  (and (mem2 x u) (mem b y v))))) (subset
  (tuple21 (set1 (tuple21 int int)) b) r
  (times b (set1 (tuple21 int int)) (t2tb4 u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int (set (tuple2 Int Int))))) (u (set Int))
  (v (set (set (tuple2 Int Int)))))
  (= (subset (tuple21 int (set1 (tuple21 int int))) (t2tb26 r)
  (times (set1 (tuple21 int int)) int (t2tb u) (t2tb4 v)))
  (forall ((x Int) (y (set (tuple2 Int Int))))
  (=> (mem (tuple21 int (set1 (tuple21 int int)))
  (Tuple2 int (set1 (tuple21 int int)) (t2tb1 x) (t2tb5 y)) (t2tb26 r))
  (and (mem1 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int Int))) (u (set Int)) (v (set Int)))
  (= (subset (tuple21 int int) (t2tb5 r) (times int int (t2tb u) (t2tb v)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 r))
  (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set Int)) (v uni))
  (and
  (=> (subset (tuple21 int b) r (times b int (t2tb u) v))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) r)
  (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) r)
  (and (mem1 x u) (mem b y v))))) (subset (tuple21 int b) r
  (times b int (t2tb u) v)))))))

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
  (forall ((b ty))
  (forall ((s (set (set (tuple2 Int Int)))) (x (set (tuple2 Int Int)))
  (y uni))
  (! (=> (sort b y)
     (=> (mem2 x s)
     (= (apply b (set1 (tuple21 int int))
        (times b (set1 (tuple21 int int)) (t2tb4 s) (add b y (empty b)))
        (t2tb5 x)) y))) :pattern ((apply b (set1 (tuple21 int int))
                                  (times b (set1 (tuple21 int int)) (t2tb4 s)
                                  (add b y (empty b))) (t2tb5 x))) ))))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (x Int) (y uni))
  (! (=> (sort b y)
     (=> (mem1 x s)
     (= (apply b int (times b int (t2tb s) (add b y (empty b))) (t2tb1 x)) y))) :pattern (
  (apply b int (times b int (t2tb s) (add b y (empty b))) (t2tb1 x))) ))))

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
  (forall ((e1 ty))
  (forall ((x uni) (y (set (tuple2 Int Int))) (r uni)
  (f (set (set (tuple2 Int Int)))))
  (=> (subset (set1 (tuple21 int int)) (t2tb4 f)
  (ran (set1 (tuple21 int int)) e1 r))
  (= (mem (tuple21 e1 (set1 (tuple21 int int)))
  (Tuple2 e1 (set1 (tuple21 int int)) x (t2tb5 y))
  (range_restriction (set1 (tuple21 int int)) e1 r (t2tb4 f)))
  (and (mem (tuple21 e1 (set1 (tuple21 int int)))
  (Tuple2 e1 (set1 (tuple21 int int)) x (t2tb5 y)) r) (mem2 y f)))))))

;; range_restriction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y Int) (r uni) (f (set Int)))
  (=> (subset int (t2tb f) (ran int e1 r))
  (= (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb1 y))
  (range_restriction int e1 r (t2tb f)))
  (and (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb1 y)) r) (mem1 y f)))))))

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
  (forall ((e1 ty))
  (forall ((x uni) (y (set (tuple2 Int Int))) (r uni)
  (f (set (set (tuple2 Int Int)))))
  (= (mem (tuple21 e1 (set1 (tuple21 int int)))
  (Tuple2 e1 (set1 (tuple21 int int)) x (t2tb5 y))
  (range_substraction (set1 (tuple21 int int)) e1 r (t2tb4 f)))
  (and (mem (tuple21 e1 (set1 (tuple21 int int)))
  (Tuple2 e1 (set1 (tuple21 int int)) x (t2tb5 y)) r) (not (mem2 y f)))))))

;; range_substraction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y Int) (r uni) (f (set Int)))
  (= (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb1 y))
  (range_substraction int e1 r (t2tb f)))
  (and (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb1 y)) r) (not (mem1 y f)))))))

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
  (forall ((e2 ty))
  (forall ((x (set (tuple2 Int Int))) (y uni) (r uni)
  (f (set (set (tuple2 Int Int)))))
  (= (mem (tuple21 (set1 (tuple21 int int)) e2)
  (Tuple2 (set1 (tuple21 int int)) e2 (t2tb5 x) y)
  (domain_restriction e2 (set1 (tuple21 int int)) (t2tb4 f) r))
  (and (mem (tuple21 (set1 (tuple21 int int)) e2)
  (Tuple2 (set1 (tuple21 int int)) e2 (t2tb5 x) y) r) (mem2 x f))))))

;; domain_restriction_def
  (assert
  (forall ((e2 ty))
  (forall ((x Int) (y uni) (r uni) (f (set Int)))
  (= (mem (tuple21 int e2) (Tuple2 int e2 (t2tb1 x) y)
  (domain_restriction e2 int (t2tb f) r))
  (and (mem (tuple21 int e2) (Tuple2 int e2 (t2tb1 x) y) r) (mem1 x f))))))

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
  (forall ((e2 ty))
  (forall ((x (set (tuple2 Int Int))) (y uni) (r uni)
  (f (set (set (tuple2 Int Int)))))
  (=> (subset (set1 (tuple21 int int)) (t2tb4 f)
  (dom e2 (set1 (tuple21 int int)) r))
  (= (mem (tuple21 (set1 (tuple21 int int)) e2)
  (Tuple2 (set1 (tuple21 int int)) e2 (t2tb5 x) y)
  (domain_substraction e2 (set1 (tuple21 int int)) (t2tb4 f) r))
  (and (mem (tuple21 (set1 (tuple21 int int)) e2)
  (Tuple2 (set1 (tuple21 int int)) e2 (t2tb5 x) y) r) (not (mem2 x f))))))))

;; domain_substraction_def
  (assert
  (forall ((e2 ty))
  (forall ((x Int) (y uni) (r uni) (f (set Int)))
  (=> (subset int (t2tb f) (dom e2 int r))
  (= (mem (tuple21 int e2) (Tuple2 int e2 (t2tb1 x) y)
  (domain_substraction e2 int (t2tb f) r))
  (and (mem (tuple21 int e2) (Tuple2 int e2 (t2tb1 x) y) r) (not (mem1 x f))))))))

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
  (forall ((b ty))
  (forall ((x (set (tuple2 Int Int))) (y uni) (q uni) (r uni))
  (= (mem (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y)
  (infix_lspl b (set1 (tuple21 int int)) q r))
  (ite (mem2 x (tb2t4 (dom b (set1 (tuple21 int int)) r))) (mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) r) (mem
  (tuple21 (set1 (tuple21 int int)) b)
  (Tuple2 (set1 (tuple21 int int)) b (t2tb5 x) y) q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni) (q uni) (r uni))
  (= (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (infix_lspl b int q r))
  (ite (mem1 x (tb2t (dom b int r))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb1 x) y) r) (mem (tuple21 int b)
  (Tuple2 int b (t2tb1 x) y) q))))))

;; overriding_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni) (q uni) (r uni))
  (= (mem (tuple21 a b) (Tuple2 a b x y) (infix_lspl b a q r))
  (ite (mem a x (dom b a r)) (mem (tuple21 a b) (Tuple2 a b x y) r) (mem
  (tuple21 a b) (Tuple2 a b x y) q))))))

;; function_overriding
  (assert
  (forall ((s (set Int)) (t (set Int)) (f (set (tuple2 Int Int)))
  (g (set (tuple2 Int Int))))
  (=>
  (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2 g
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))) (mem2
  (tb2t5 (infix_lspl int int (t2tb5 f) (t2tb5 g)))
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))))))

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
  (forall ((b ty))
  (forall ((s (set (set (tuple2 Int Int)))) (t uni) (f uni) (g uni)
  (x (set (tuple2 Int Int))))
  (! (=>
     (and (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
     (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)) (mem
     (set1 (tuple21 (set1 (tuple21 int int)) b)) g
     (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)))
     (=> (mem2 x (tb2t4 (dom b (set1 (tuple21 int int)) g)))
     (= (apply b (set1 (tuple21 int int))
        (infix_lspl b (set1 (tuple21 int int)) f g) (t2tb5 x)) (apply b
                                                               (set1
                                                               (tuple21 
                                                               int int)) g
                                                               (t2tb5 x))))) :pattern ((mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)) (mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) g
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (apply b (set1 (tuple21 int int))
  (infix_lspl b (set1 (tuple21 int int)) f g) (t2tb5 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((s (set Int)) (t (set Int)) (f (set (tuple2 Int Int)))
  (g (set (tuple2 Int Int))) (x Int))
  (! (=>
     (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2 g
     (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))))
     (=> (mem1 x (tb2t (dom int int (t2tb5 g))))
     (= (tb2t1
        (apply int int (infix_lspl int int (t2tb5 f) (t2tb5 g)) (t2tb1 x))) 
     (tb2t1 (apply int int (t2tb5 g) (t2tb1 x)))))) :pattern ((mem2
  f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2 g
  (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (tb2t1 (apply int int (infix_lspl int int (t2tb5 f) (t2tb5 g)) (t2tb1 x)))) )))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t)) (mem
     (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb s) t)))
     (=> (mem1 x (tb2t (dom b int g)))
     (= (apply b int (infix_lspl b int f g) (t2tb1 x)) (apply b int g
                                                       (t2tb1 x))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t)) (mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb s) t))
  (apply b int (infix_lspl b int f g) (t2tb1 x))) ))))

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
  (forall ((s (set (set (tuple2 Int Int)))) (t uni) (f uni) (g uni)
  (x (set (tuple2 Int Int))))
  (! (=>
     (and (mem (set1 (tuple21 (set1 (tuple21 int int)) b)) f
     (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)) (mem
     (set1 (tuple21 (set1 (tuple21 int int)) b)) g
     (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t)))
     (=> (not (mem2 x (tb2t4 (dom b (set1 (tuple21 int int)) g))))
     (=> (mem2 x (tb2t4 (dom b (set1 (tuple21 int int)) f)))
     (= (apply b (set1 (tuple21 int int))
        (infix_lspl b (set1 (tuple21 int int)) f g) (t2tb5 x)) (apply b
                                                               (set1
                                                               (tuple21 
                                                               int int)) f
                                                               (t2tb5 x)))))) :pattern ((mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) f
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (apply b (set1 (tuple21 int int))
  (infix_lspl b (set1 (tuple21 int int)) f g) (t2tb5 x))) :pattern ((mem
  (set1 (tuple21 (set1 (tuple21 int int)) b)) g
  (infix_plmngt b (set1 (tuple21 int int)) (t2tb4 s) t))
  (apply b (set1 (tuple21 int int))
  (infix_lspl b (set1 (tuple21 int int)) f g) (t2tb5 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((s (set Int)) (t (set Int)) (f (set (tuple2 Int Int)))
  (g (set (tuple2 Int Int))) (x Int))
  (! (=>
     (and (mem2 f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))) (mem2 g
     (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t)))))
     (=> (not (mem1 x (tb2t (dom int int (t2tb5 g)))))
     (=> (mem1 x (tb2t (dom int int (t2tb5 f))))
     (= (tb2t1
        (apply int int (infix_lspl int int (t2tb5 f) (t2tb5 g)) (t2tb1 x))) 
     (tb2t1 (apply int int (t2tb5 f) (t2tb1 x))))))) :pattern ((mem2
  f (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (tb2t1 (apply int int (infix_lspl int int (t2tb5 f) (t2tb5 g)) (t2tb1 x)))) :pattern ((mem2
  g (tb2t4 (infix_plmngt int int (t2tb s) (t2tb t))))
  (tb2t1 (apply int int (infix_lspl int int (t2tb5 f) (t2tb5 g)) (t2tb1 x)))) )))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t)) (mem
     (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb s) t)))
     (=> (not (mem1 x (tb2t (dom b int g))))
     (=> (mem1 x (tb2t (dom b int f)))
     (= (apply b int (infix_lspl b int f g) (t2tb1 x)) (apply b int f
                                                       (t2tb1 x)))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb s) t))
  (apply b int (infix_lspl b int f g) (t2tb1 x))) :pattern ((mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb s) t))
  (apply b int (infix_lspl b int f g) (t2tb1 x))) ))))

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

(declare-sort enum_t_BOOM_MOVEMENT_ORDER 0)

(declare-fun enum_t_BOOM_MOVEMENT_ORDER1 () ty)

(declare-fun E_go_up () enum_t_BOOM_MOVEMENT_ORDER)

(declare-fun E_go_down () enum_t_BOOM_MOVEMENT_ORDER)

(declare-fun match_enum_t_BOOM_MOVEMENT_ORDER (ty enum_t_BOOM_MOVEMENT_ORDER
  uni uni) uni)

;; match_enum_t_BOOM_MOVEMENT_ORDER_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_BOOM_MOVEMENT_ORDER) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_BOOM_MOVEMENT_ORDER a x x1 x2)))))

;; match_enum_t_BOOM_MOVEMENT_ORDER_E_go_up
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_BOOM_MOVEMENT_ORDER a E_go_up z z1) z)))))

;; match_enum_t_BOOM_MOVEMENT_ORDER_E_go_down
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_BOOM_MOVEMENT_ORDER a E_go_down z z1) z1)))))

(declare-fun index_enum_t_BOOM_MOVEMENT_ORDER (enum_t_BOOM_MOVEMENT_ORDER) Int)

;; index_enum_t_BOOM_MOVEMENT_ORDER_E_go_up
  (assert (= (index_enum_t_BOOM_MOVEMENT_ORDER E_go_up) 0))

;; index_enum_t_BOOM_MOVEMENT_ORDER_E_go_down
  (assert (= (index_enum_t_BOOM_MOVEMENT_ORDER E_go_down) 1))

;; enum_t_BOOM_MOVEMENT_ORDER_inversion
  (assert
  (forall ((u enum_t_BOOM_MOVEMENT_ORDER))
  (or (= u E_go_up) (= u E_go_down))))

(declare-fun set_enum_t_BOOM_MOVEMENT_ORDER () (set enum_t_BOOM_MOVEMENT_ORDER))

(declare-fun t2tb8 ((set enum_t_BOOM_MOVEMENT_ORDER)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_BOOM_MOVEMENT_ORDER))) (sort
  (set1 enum_t_BOOM_MOVEMENT_ORDER1) (t2tb8 x))))

(declare-fun tb2t8 (uni) (set enum_t_BOOM_MOVEMENT_ORDER))

;; BridgeL
  (assert
  (forall ((i (set enum_t_BOOM_MOVEMENT_ORDER)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_BOOM_MOVEMENT_ORDER1) j) (= (t2tb8 (tb2t8 j)) j)) :pattern (
  (t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 (enum_t_BOOM_MOVEMENT_ORDER) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_t_BOOM_MOVEMENT_ORDER)) (sort enum_t_BOOM_MOVEMENT_ORDER1
  (t2tb9 x))))

(declare-fun tb2t9 (uni) enum_t_BOOM_MOVEMENT_ORDER)

;; BridgeL
  (assert
  (forall ((i enum_t_BOOM_MOVEMENT_ORDER))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_BOOM_MOVEMENT_ORDER1 j) (= (t2tb9 (tb2t9 j)) j)) :pattern (
  (t2tb9 (tb2t9 j))) )))

;; set_enum_t_BOOM_MOVEMENT_ORDER_axiom
  (assert
  (forall ((x enum_t_BOOM_MOVEMENT_ORDER)) (mem enum_t_BOOM_MOVEMENT_ORDER1
  (t2tb9 x) (t2tb8 set_enum_t_BOOM_MOVEMENT_ORDER))))

(declare-sort enum_t_BOOM_TYPE 0)

(declare-fun enum_t_BOOM_TYPE1 () ty)

(declare-fun E_primary_boom () enum_t_BOOM_TYPE)

(declare-fun E_secondary_boom () enum_t_BOOM_TYPE)

(declare-fun match_enum_t_BOOM_TYPE (ty enum_t_BOOM_TYPE uni uni) uni)

;; match_enum_t_BOOM_TYPE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_BOOM_TYPE) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_BOOM_TYPE a x x1 x2)))))

;; match_enum_t_BOOM_TYPE_E_primary_boom
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_BOOM_TYPE a E_primary_boom z z1) z)))))

;; match_enum_t_BOOM_TYPE_E_secondary_boom
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_BOOM_TYPE a E_secondary_boom z z1) z1)))))

(declare-fun index_enum_t_BOOM_TYPE (enum_t_BOOM_TYPE) Int)

;; index_enum_t_BOOM_TYPE_E_primary_boom
  (assert (= (index_enum_t_BOOM_TYPE E_primary_boom) 0))

;; index_enum_t_BOOM_TYPE_E_secondary_boom
  (assert (= (index_enum_t_BOOM_TYPE E_secondary_boom) 1))

;; enum_t_BOOM_TYPE_inversion
  (assert
  (forall ((u enum_t_BOOM_TYPE))
  (or (= u E_primary_boom) (= u E_secondary_boom))))

(declare-fun set_enum_t_BOOM_TYPE () (set enum_t_BOOM_TYPE))

(declare-fun t2tb10 ((set enum_t_BOOM_TYPE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_BOOM_TYPE))) (sort (set1 enum_t_BOOM_TYPE1)
  (t2tb10 x))))

(declare-fun tb2t10 (uni) (set enum_t_BOOM_TYPE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_BOOM_TYPE)))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_BOOM_TYPE1) j) (= (t2tb10 (tb2t10 j)) j)) :pattern (
  (t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 (enum_t_BOOM_TYPE) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_t_BOOM_TYPE)) (sort enum_t_BOOM_TYPE1 (t2tb11 x))))

(declare-fun tb2t11 (uni) enum_t_BOOM_TYPE)

;; BridgeL
  (assert
  (forall ((i enum_t_BOOM_TYPE))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_BOOM_TYPE1 j) (= (t2tb11 (tb2t11 j)) j)) :pattern (
  (t2tb11 (tb2t11 j))) )))

;; set_enum_t_BOOM_TYPE_axiom
  (assert
  (forall ((x enum_t_BOOM_TYPE)) (mem enum_t_BOOM_TYPE1 (t2tb11 x)
  (t2tb10 set_enum_t_BOOM_TYPE))))

(declare-sort enum_t_DETECTOR 0)

(declare-fun enum_t_DETECTOR1 () ty)

(declare-fun E_adc_detector () enum_t_DETECTOR)

(declare-fun E_bdc_detector () enum_t_DETECTOR)

(declare-fun match_enum_t_DETECTOR (ty enum_t_DETECTOR uni uni) uni)

;; match_enum_t_DETECTOR_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_DETECTOR) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_DETECTOR a x x1 x2)))))

;; match_enum_t_DETECTOR_E_adc_detector
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_DETECTOR a E_adc_detector z z1) z)))))

;; match_enum_t_DETECTOR_E_bdc_detector
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_DETECTOR a E_bdc_detector z z1) z1)))))

(declare-fun index_enum_t_DETECTOR (enum_t_DETECTOR) Int)

;; index_enum_t_DETECTOR_E_adc_detector
  (assert (= (index_enum_t_DETECTOR E_adc_detector) 0))

;; index_enum_t_DETECTOR_E_bdc_detector
  (assert (= (index_enum_t_DETECTOR E_bdc_detector) 1))

;; enum_t_DETECTOR_inversion
  (assert
  (forall ((u enum_t_DETECTOR))
  (or (= u E_adc_detector) (= u E_bdc_detector))))

(declare-fun set_enum_t_DETECTOR () (set enum_t_DETECTOR))

(declare-fun t2tb12 ((set enum_t_DETECTOR)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_DETECTOR))) (sort (set1 enum_t_DETECTOR1)
  (t2tb12 x))))

(declare-fun tb2t12 (uni) (set enum_t_DETECTOR))

;; BridgeL
  (assert
  (forall ((i (set enum_t_DETECTOR)))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_DETECTOR1) j) (= (t2tb12 (tb2t12 j)) j)) :pattern (
  (t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 (enum_t_DETECTOR) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_DETECTOR)) (sort enum_t_DETECTOR1 (t2tb13 x))))

(declare-fun tb2t13 (uni) enum_t_DETECTOR)

;; BridgeL
  (assert
  (forall ((i enum_t_DETECTOR))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_DETECTOR1 j) (= (t2tb13 (tb2t13 j)) j)) :pattern (
  (t2tb13 (tb2t13 j))) )))

;; set_enum_t_DETECTOR_axiom
  (assert
  (forall ((x enum_t_DETECTOR)) (mem enum_t_DETECTOR1 (t2tb13 x)
  (t2tb12 set_enum_t_DETECTOR))))

(declare-sort enum_t_GATE 0)

(declare-fun enum_t_GATE1 () ty)

(declare-fun E_inbound_lineside_gate () enum_t_GATE)

(declare-fun E_outbound_lineside_gate () enum_t_GATE)

(declare-fun match_enum_t_GATE (ty enum_t_GATE uni uni) uni)

;; match_enum_t_GATE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_GATE) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_GATE a x x1 x2)))))

;; match_enum_t_GATE_E_inbound_lineside_gate
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_GATE a E_inbound_lineside_gate z z1) z)))))

;; match_enum_t_GATE_E_outbound_lineside_gate
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_GATE a E_outbound_lineside_gate z z1) z1)))))

(declare-fun index_enum_t_GATE (enum_t_GATE) Int)

;; index_enum_t_GATE_E_inbound_lineside_gate
  (assert (= (index_enum_t_GATE E_inbound_lineside_gate) 0))

;; index_enum_t_GATE_E_outbound_lineside_gate
  (assert (= (index_enum_t_GATE E_outbound_lineside_gate) 1))

;; enum_t_GATE_inversion
  (assert
  (forall ((u enum_t_GATE))
  (or (= u E_inbound_lineside_gate) (= u E_outbound_lineside_gate))))

(declare-fun set_enum_t_GATE () (set enum_t_GATE))

(declare-fun t2tb14 ((set enum_t_GATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_GATE))) (sort (set1 enum_t_GATE1) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set enum_t_GATE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_GATE)))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_GATE1) j) (= (t2tb14 (tb2t14 j)) j)) :pattern (
  (t2tb14 (tb2t14 j))) )))

(declare-fun t2tb15 (enum_t_GATE) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_GATE)) (sort enum_t_GATE1 (t2tb15 x))))

(declare-fun tb2t15 (uni) enum_t_GATE)

;; BridgeL
  (assert
  (forall ((i enum_t_GATE))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_GATE1 j) (= (t2tb15 (tb2t15 j)) j)) :pattern ((t2tb15
                                                                    (tb2t15
                                                                    j))) )))

;; set_enum_t_GATE_axiom
  (assert
  (forall ((x enum_t_GATE)) (mem enum_t_GATE1 (t2tb15 x)
  (t2tb14 set_enum_t_GATE))))

(declare-sort enum_t_LINE 0)

(declare-fun enum_t_LINE1 () ty)

(declare-fun E_inbound_line () enum_t_LINE)

(declare-fun E_outbound_line () enum_t_LINE)

(declare-fun match_enum_t_LINE (ty enum_t_LINE uni uni) uni)

;; match_enum_t_LINE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_LINE) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_LINE a x x1 x2)))))

;; match_enum_t_LINE_E_inbound_line
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_LINE a E_inbound_line z z1) z)))))

;; match_enum_t_LINE_E_outbound_line
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_LINE a E_outbound_line z z1) z1)))))

(declare-fun index_enum_t_LINE (enum_t_LINE) Int)

;; index_enum_t_LINE_E_inbound_line
  (assert (= (index_enum_t_LINE E_inbound_line) 0))

;; index_enum_t_LINE_E_outbound_line
  (assert (= (index_enum_t_LINE E_outbound_line) 1))

;; enum_t_LINE_inversion
  (assert
  (forall ((u enum_t_LINE)) (or (= u E_inbound_line) (= u E_outbound_line))))

(declare-fun set_enum_t_LINE () (set enum_t_LINE))

(declare-fun t2tb16 ((set enum_t_LINE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_LINE))) (sort (set1 enum_t_LINE1) (t2tb16 x))))

(declare-fun tb2t16 (uni) (set enum_t_LINE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_LINE)))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_LINE1) j) (= (t2tb16 (tb2t16 j)) j)) :pattern (
  (t2tb16 (tb2t16 j))) )))

(declare-fun t2tb17 (enum_t_LINE) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_LINE)) (sort enum_t_LINE1 (t2tb17 x))))

(declare-fun tb2t17 (uni) enum_t_LINE)

;; BridgeL
  (assert
  (forall ((i enum_t_LINE))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_LINE1 j) (= (t2tb17 (tb2t17 j)) j)) :pattern ((t2tb17
                                                                    (tb2t17
                                                                    j))) )))

;; set_enum_t_LINE_axiom
  (assert
  (forall ((x enum_t_LINE)) (mem enum_t_LINE1 (t2tb17 x)
  (t2tb16 set_enum_t_LINE))))

(assert
;; ValuesLemmas_2
 ;; File "POwhy_bpo2why/RCS3/Configuration_i.why", line 266, characters 7-21
  (not (mem2 (id1 (mk 1 21)) (seq2 (mk 1 21)))))
(check-sat)
