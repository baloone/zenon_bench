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

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (Int (set Int)) Bool)

(declare-fun mem2 ((set Int) (set (set Int))) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun t2tb ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb x))))

(declare-fun tb2t (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni)) (! (= (t2tb (tb2t j)) j) :pattern ((t2tb (tb2t j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))))
  (= (infix_eqeq (set1 int) (t2tb s1) (t2tb s2))
  (forall ((x (set Int))) (= (mem2 x s1) (mem2 x s2))))))

(declare-fun t2tb1 ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb1 x))))

(declare-fun tb2t1 (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int))) (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb1 (tb2t1 j)) j) :pattern ((t2tb1 (tb2t1 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (infix_eqeq int (t2tb1 s1) (t2tb1 s2))
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
  (forall ((s1 (set (set Int))) (s2 (set (set Int))))
  (= (subset (set1 int) (t2tb s1) (t2tb s2))
  (forall ((x (set Int))) (=> (mem2 x s1) (mem2 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (subset int (t2tb1 s1) (t2tb1 s2))
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

(declare-fun empty1 () (set Int))

(declare-fun empty2 () (set (set Int)))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set (set Int))))
  (= (is_empty (set1 int) (t2tb s))
  (forall ((x (set Int))) (not (mem2 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set Int)))
  (= (is_empty int (t2tb1 s)) (forall ((x Int)) (not (mem1 x s))))))

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (is_empty (set1 int) (t2tb empty2)))

;; empty_def1
  (assert (is_empty int (t2tb1 empty1)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert (forall ((x (set Int))) (not (mem2 x empty2))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem1 x empty1))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

;; add_def1
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (forall ((s (set (set Int))))
  (= (mem2 x (tb2t (add (set1 int) (t2tb1 y) (t2tb s))))
  (or (= x y) (mem2 x s))))))

(declare-fun t2tb2 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb2 x))))

(declare-fun tb2t2 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb2 (tb2t2 j)) j) :pattern ((t2tb2 (tb2t2 j))) )))

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int)))
  (= (mem1 x (tb2t1 (add int (t2tb2 y) (t2tb1 s)))) (or (= x y) (mem1 x s))))))

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
  (forall ((x (set Int)) (y (set Int)) (s (set (set Int))))
  (= (mem2 x (tb2t (remove (set1 int) (t2tb1 y) (t2tb s))))
  (and (not (= x y)) (mem2 x s)))))

;; remove_def1
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem1 x (tb2t1 (remove int (t2tb2 y) (t2tb1 s))))
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
  (forall ((x (set Int)) (s (set (set Int))))
  (=> (mem2 x s)
  (= (tb2t (add (set1 int) (t2tb1 x) (remove (set1 int) (t2tb1 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem1 x s)
  (= (tb2t1 (add int (t2tb2 x) (remove int (t2tb2 x) (t2tb1 s)))) s))))

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
  (forall ((s1 (set (set Int))) (s2 (set (set Int))) (x (set Int)))
  (= (mem2 x (tb2t (union (set1 int) (t2tb s1) (t2tb s2))))
  (or (mem2 x s1) (mem2 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t1 (union int (t2tb1 s1) (t2tb1 s2))))
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
  (forall ((s1 (set (set Int))) (s2 (set (set Int))) (x (set Int)))
  (= (mem2 x (tb2t (inter (set1 int) (t2tb s1) (t2tb s2))))
  (and (mem2 x s1) (mem2 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t1 (inter int (t2tb1 s1) (t2tb1 s2))))
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
  (forall ((s1 (set (set Int))) (s2 (set (set Int))) (x (set Int)))
  (= (mem2 x (tb2t (diff (set1 int) (t2tb s1) (t2tb s2))))
  (and (mem2 x s1) (not (mem2 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t1 (diff int (t2tb1 s1) (t2tb1 s2))))
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
  (forall ((s (set (set Int))))
  (=> (not (is_empty (set1 int) (t2tb s))) (mem2
  (tb2t1 (choose (set1 int) (t2tb s))) s))))

;; choose_def
  (assert
  (forall ((s (set Int)))
  (=> (not (is_empty int (t2tb1 s))) (mem1 (tb2t2 (choose int (t2tb1 s))) s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert (forall ((x (set Int))) (mem2 x (tb2t (all (set1 int))))))

;; all_def
  (assert (forall ((x Int)) (mem1 x (tb2t1 (all int)))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

(declare-fun t2tb3 (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb3 x))))

(declare-fun tb2t3 (uni) Bool)

;; BridgeL
  (assert
  (forall ((i Bool)) (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb3 (tb2t3 j)) j)) :pattern ((t2tb3 (tb2t3 j))) )))

(declare-fun t2tb4 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool))) (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb4 (tb2t4 j)) j)) :pattern ((t2tb4
                                                                 (tb2t4 j))) )))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb3 x) (t2tb4 b_bool))))

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
  (assert (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) empty1))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t1 (add int (t2tb2 b) (t2tb1 (mk a (- b 1)))))))))

(declare-fun power (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power a x)))))

(declare-fun power1 ((set Int)) (set (set Int)))

;; mem_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem2 x (power1 y)) (subset int (t2tb1 x) (t2tb1 y))) :pattern ((mem2
  x (power1 y))) )))

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

(declare-fun t2tb5 ((set (set (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set Int))))) (sort (set1 (set1 (set1 int)))
  (t2tb5 x))))

(declare-fun tb2t5 (uni) (set (set (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (set Int)))))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb5 (tb2t5 j)) j) :pattern ((t2tb5 (tb2t5 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (set Int))) (y (set (set Int))))
  (! (= (mem (set1 (set1 int)) (t2tb x)
     (non_empty_power (set1 int) (t2tb y)))
     (and (subset (set1 int) (t2tb x) (t2tb y)) (not (= x empty2)))) :pattern ((mem
  (set1 (set1 int)) (t2tb x) (non_empty_power (set1 int) (t2tb y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem2 x (tb2t (non_empty_power int (t2tb1 y))))
     (and (subset int (t2tb1 x) (t2tb1 y)) (not (= x empty1)))) :pattern ((mem2
  x (tb2t (non_empty_power int (t2tb1 y))))) )))

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
  (forall ((f uni) (s uni) (t (set (set Int))))
  (and
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (relation (set1 int) a s (t2tb t)))
  (forall ((x uni) (y (set Int)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (=>
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) f)
  (and (mem a x s) (mem2 y t))))) (mem (set1 (tuple21 a (set1 int))) f
  (relation (set1 int) a s (t2tb t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (relation int a s (t2tb1 t)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) f)
  (and (mem a x s) (mem1 y t))))) (mem (set1 (tuple21 a int)) f
  (relation int a s (t2tb1 t))))))))

(declare-fun t2tb6 ((set (set (tuple2 (set Int) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (set Int)))))) (sort
  (set1 (set1 (tuple21 (set1 int) (set1 int)))) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set (set (tuple2 (set Int) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (set Int))))))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb6 (tb2t6 j)) j) :pattern ((t2tb6 (tb2t6 j))) )))

(declare-fun t2tb7 ((set (tuple2 (set Int) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (set Int))))) (sort
  (set1 (tuple21 (set1 int) (set1 int))) (t2tb7 x))))

(declare-fun tb2t7 (uni) (set (tuple2 (set Int) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (set Int)))))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb7 (tb2t7 j)) j) :pattern ((t2tb7 (tb2t7 j))) )))

(declare-fun t2tb8 ((tuple2 (set Int) (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (set Int)))) (sort
  (tuple21 (set1 int) (set1 int)) (t2tb8 x))))

(declare-fun tb2t8 (uni) (tuple2 (set Int) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (set Int))))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb8 (tb2t8 j)) j) :pattern ((t2tb8 (tb2t8 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set Int) (set Int)))) (s (set (set Int)))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb7 f)
  (relation (set1 int) (set1 int) (t2tb s) (t2tb t)))
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y)) (t2tb7 f))
  (and (mem2 x s) (mem2 y t)))))))

(declare-fun t2tb9 ((set (set (tuple2 (set Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) Int))))) (sort
  (set1 (set1 (tuple21 (set1 int) int))) (t2tb9 x))))

(declare-fun tb2t9 (uni) (set (set (tuple2 (set Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) Int)))))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb9 (tb2t9 j)) j) :pattern ((t2tb9 (tb2t9 j))) )))

(declare-fun t2tb10 ((set (tuple2 (set Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) Int)))) (sort
  (set1 (tuple21 (set1 int) int)) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set (tuple2 (set Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) Int))))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb10 (tb2t10 j)) j) :pattern ((t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 ((tuple2 (set Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) Int))) (sort (tuple21 (set1 int) int)
  (t2tb11 x))))

(declare-fun tb2t11 (uni) (tuple2 (set Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) Int)))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb11 (tb2t11 j)) j) :pattern ((t2tb11 (tb2t11 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set Int) Int))) (s (set (set Int)))
  (t (set Int)))
  (= (mem (set1 (tuple21 (set1 int) int)) (t2tb10 f)
  (relation int (set1 int) (t2tb s) (t2tb1 t)))
  (forall ((x (set Int)) (y Int))
  (=> (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y)) (t2tb10 f))
  (and (mem2 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (relation b (set1 int) (t2tb s) t))
  (forall ((x (set Int)) (y uni))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (=>
  (forall ((x (set Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) f)
  (and (mem2 x s) (mem b y t))))) (mem (set1 (tuple21 (set1 int) b)) f
  (relation b (set1 int) (t2tb s) t)))))))

(declare-fun t2tb12 ((set (set (tuple2 Int (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (set Int)))))) (sort
  (set1 (set1 (tuple21 int (set1 int)))) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (set (tuple2 Int (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (set Int))))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 ((set (tuple2 Int (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (set Int))))) (sort
  (set1 (tuple21 int (set1 int))) (t2tb13 x))))

(declare-fun tb2t13 (uni) (set (tuple2 Int (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (set Int)))))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb13 (tb2t13 j)) j) :pattern ((t2tb13 (tb2t13 j))) )))

(declare-fun t2tb14 ((tuple2 Int (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (set Int)))) (sort (tuple21 int (set1 int))
  (t2tb14 x))))

(declare-fun tb2t14 (uni) (tuple2 Int (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (set Int))))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int (set Int)))) (s (set Int))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 int (set1 int))) (t2tb13 f)
  (relation (set1 int) int (t2tb1 s) (t2tb t)))
  (forall ((x Int) (y (set Int)))
  (=> (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y)) (t2tb13 f))
  (and (mem1 x s) (mem2 y t)))))))

(declare-fun t2tb15 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

(declare-fun t2tb16 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb16 (tb2t16 j)) j) :pattern ((t2tb16 (tb2t16 j))) )))

(declare-fun t2tb17 ((tuple2 Int Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Int))) (sort (tuple21 int int) (t2tb17 x))))

(declare-fun tb2t17 (uni) (tuple2 Int Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Int)))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb16 f)
  (relation int int (t2tb1 s) (t2tb1 t)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y)) (t2tb16 f))
  (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (relation b int (t2tb1 s) t))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) f)
  (and (mem1 x s) (mem b y t))))) (mem (set1 (tuple21 int b)) f
  (relation b int (t2tb1 s) t)))))))

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
  (forall ((r uni) (dom uni) (y (set Int)))
  (! (and
     (=> (mem2 y (tb2t (image (set1 int) a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a (set1 int))
     (Tuple2 a (set1 int) x (t2tb1 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a (set1 int))
     (Tuple2 a (set1 int) x (t2tb1 y)) r))) (mem2 y
     (tb2t (image (set1 int) a r dom))))) :pattern ((mem2
  y (tb2t (image (set1 int) a r dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y Int))
  (! (and
     (=> (mem1 y (tb2t1 (image int a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) r)))
     (mem1 y (tb2t1 (image int a r dom))))) :pattern ((mem1
  y (tb2t1 (image int a r dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set Int) (set Int)))) (dom (set (set Int)))
  (y (set Int)))
  (! (= (mem2 y (tb2t (image (set1 int) (set1 int) (t2tb7 r) (t2tb dom))))
     (exists ((x (set Int)))
     (and (mem2 x dom) (mem (tuple21 (set1 int) (set1 int))
     (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y)) (t2tb7 r))))) :pattern ((mem2
  y (tb2t (image (set1 int) (set1 int) (t2tb7 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set Int) Int))) (dom (set (set Int))) (y Int))
  (! (= (mem1 y (tb2t1 (image int (set1 int) (t2tb10 r) (t2tb dom))))
     (exists ((x (set Int)))
     (and (mem2 x dom) (mem (tuple21 (set1 int) int)
     (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y)) (t2tb10 r))))) :pattern ((mem1
  y (tb2t1 (image int (set1 int) (t2tb10 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set Int))) (y uni))
  (! (= (mem b y (image b (set1 int) r (t2tb dom)))
     (exists ((x (set Int)))
     (and (mem2 x dom) (mem (tuple21 (set1 int) b)
     (Tuple2 (set1 int) b (t2tb1 x) y) r)))) :pattern ((mem
  b y (image b (set1 int) r (t2tb dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int (set Int)))) (dom (set Int)) (y (set Int)))
  (! (= (mem2 y (tb2t (image (set1 int) int (t2tb13 r) (t2tb1 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int (set1 int))
     (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y)) (t2tb13 r))))) :pattern ((mem2
  y (tb2t (image (set1 int) int (t2tb13 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom (set Int)) (y Int))
  (! (= (mem1 y (tb2t1 (image int int (t2tb16 r) (t2tb1 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int int)
     (Tuple2 int int (t2tb2 x) (t2tb2 y)) (t2tb16 r))))) :pattern ((mem1
  y (tb2t1 (image int int (t2tb16 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (y uni))
  (! (= (mem b y (image b int r (t2tb1 dom)))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) r)))) :pattern ((mem
  b y (image b int r (t2tb1 dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (dom uni) (y uni))
  (! (and
     (=> (mem b y (image b a r dom))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a b) (Tuple2 a b x y) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a b) (Tuple2 a b x y) r))) (mem b y
     (image b a r dom)))) :pattern ((mem
  b y (image b a r dom))) ))))

;; image_union
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (s uni) (t uni))
  (= (image b a r (union a s t)) (union b (image b a r s) (image b a r t))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set Int))) (x (set Int)))
  (= (image b (set1 int) r (add (set1 int) (t2tb1 x) (t2tb dom))) (union b
                                                                  (image b
                                                                  (set1 int)
                                                                  r
                                                                  (add
                                                                  (set1 int)
                                                                  (t2tb1 x)
                                                                  (t2tb
                                                                  empty2)))
                                                                  (image b
                                                                  (set1 int)
                                                                  r
                                                                  (t2tb dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (x Int))
  (= (image b int r (add int (t2tb2 x) (t2tb1 dom))) (union b
                                                     (image b int r
                                                     (add int (t2tb2 x)
                                                     (t2tb1 empty1)))
                                                     (image b int r
                                                     (t2tb1 dom)))))))

;; image_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (dom uni) (x uni))
  (= (image b a r (add a x dom)) (union b (image b a r (add a x (empty a)))
                                 (image b a r dom))))))

(declare-fun infix_plmngt (ty ty uni uni) uni)

;; infix +->_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple21 a b)))
  (infix_plmngt b a x x1)))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set Int))))
  (and
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb t)))
  (and
  (forall ((x uni) (y (set Int)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) f)
  (and (mem a x s) (mem2 y t))))
  (forall ((x uni) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y1)) f) (mem
  (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (forall ((x uni) (y1 (set Int)) (y2 (set Int)))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y1)) f) (mem
  (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y2)) f)) (= y1 y2)))))
  (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (and
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) f)
  (and (mem a x s) (mem1 y t))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb2 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb2 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set Int) (set Int)))) (s (set (set Int)))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb7 f)
  (infix_plmngt (set1 int) (set1 int) (t2tb s) (t2tb t)))
  (and
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y)) (t2tb7 f))
  (and (mem2 x s) (mem2 y t))))
  (forall ((x (set Int)) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y1)) (t2tb7 f)) (mem
  (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y2)) (t2tb7 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set Int) Int))) (s (set (set Int)))
  (t (set Int)))
  (= (mem (set1 (tuple21 (set1 int) int)) (t2tb10 f)
  (infix_plmngt int (set1 int) (t2tb s) (t2tb1 t)))
  (and
  (forall ((x (set Int)) (y Int))
  (=> (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y)) (t2tb10 f))
  (and (mem2 x s) (mem1 y t))))
  (forall ((x (set Int)) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y1)) (t2tb10 f)) (mem
  (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y2))
  (t2tb10 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb s) t))
  (and
  (forall ((x (set Int)) (y uni))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) f)
  (and (mem2 x s) (mem b y t))))
  (forall ((x (set Int)) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y1) f) (mem
  (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x (set Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (forall ((x (set Int)) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y1) f) (mem
  (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y2) f)) (= y1 y2))))))
  (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int (set Int)))) (s (set Int))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 int (set1 int))) (t2tb13 f)
  (infix_plmngt (set1 int) int (t2tb1 s) (t2tb t)))
  (and
  (forall ((x Int) (y (set Int)))
  (=> (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y)) (t2tb13 f))
  (and (mem1 x s) (mem2 y t))))
  (forall ((x Int) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y1)) (t2tb13 f)) (mem
  (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y2))
  (t2tb13 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb16 f)
  (infix_plmngt int int (t2tb1 s) (t2tb1 t)))
  (and
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y)) (t2tb16 f))
  (and (mem1 x s) (mem1 y t))))
  (forall ((x Int) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y1))
  (t2tb16 f)) (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y2))
  (t2tb16 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (and
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) f)
  (and (mem1 x s) (mem b y t))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb2 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb2 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t)))))))

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
  (forall ((f uni) (s (set (set Int))) (t uni) (x (set Int)) (y uni))
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb s) t))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) f) (mem2
  x s))))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (x Int) (y uni))
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) f) (mem1 x s))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set Int))) (x uni) (y (set Int)))
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb t)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) f) (mem2
  y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (x uni) (y Int))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) f) (mem1 y t))))))

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
  (forall ((f uni) (s uni) (t (set (set Int))) (u (set (set Int))))
  (=> (subset (set1 int) (t2tb u) (t2tb t))
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb t)))
  (=>
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) f) (mem2
  y u)))) (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (u (set Int)))
  (=> (subset int (t2tb1 u) (t2tb1 t))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 u)))))))))

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
  (forall ((x (set Int)))
  (and
  (=> (mem2 x (tb2t (dom b (set1 int) r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb1 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb1 x) y) r)) (mem2 x (tb2t (dom b (set1 int) r)))))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x Int))
  (and
  (=> (mem1 x (tb2t1 (dom b int r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) r))))
  (=> (exists ((y uni)) (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) r))
  (mem1 x (tb2t1 (dom b int r)))))))))

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
  (forall ((y (set Int)))
  (and
  (=> (mem2 y (tb2t (ran (set1 int) a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a (set1 int))
  (Tuple2 a (set1 int) x (t2tb1 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a (set1 int))
  (Tuple2 a (set1 int) x (t2tb1 y)) r)) (mem2 y (tb2t (ran (set1 int) a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y Int))
  (and
  (=> (mem1 y (tb2t1 (ran int a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) r))))
  (=> (exists ((x uni)) (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) r))
  (mem1 y (tb2t1 (ran int a r)))))))))

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
  (= (tb2t (dom b (set1 int) (empty (tuple21 (set1 int) b)))) empty2)))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t1 (dom b int (empty (tuple21 int b)))) empty1)))

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
  (forall ((b ty))
  (forall ((x (set Int)) (y uni))
  (= (tb2t
     (dom b (set1 int)
     (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y)
     (empty (tuple21 (set1 int) b))))) (tb2t
                                       (add (set1 int) (t2tb1 x)
                                       (t2tb empty2)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni))
  (= (tb2t1
     (dom b int
     (add (tuple21 int b) (Tuple2 int b (t2tb2 x) y) (empty (tuple21 int b))))) 
  (tb2t1 (add int (t2tb2 x) (t2tb1 empty1)))))))

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
  (forall ((s uni) (t (set (set Int))) (x uni) (y (set Int)))
  (=> (and (mem a x s) (mem2 y t)) (mem (set1 (tuple21 a (set1 int)))
  (add (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y))
  (empty (tuple21 a (set1 int)))) (infix_plmngt (set1 int) a s (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set Int)) (x uni) (y Int))
  (=> (and (mem a x s) (mem1 y t)) (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb2 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb1 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set Int))) (t (set (set Int))) (x (set Int))
  (y (set Int)))
  (=> (and (mem2 x s) (mem2 y t)) (mem (set1 (tuple21 (set1 int) (set1 int)))
  (add (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y))
  (empty (tuple21 (set1 int) (set1 int))))
  (infix_plmngt (set1 int) (set1 int) (t2tb s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set Int))) (t (set Int)) (x (set Int)) (y Int))
  (=> (and (mem2 x s) (mem1 y t)) (mem (set1 (tuple21 (set1 int) int))
  (add (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y))
  (empty (tuple21 (set1 int) int)))
  (infix_plmngt int (set1 int) (t2tb s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (set Int))) (t uni) (x (set Int)) (y uni))
  (=> (and (mem2 x s) (mem b y t)) (mem (set1 (tuple21 (set1 int) b))
  (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y)
  (empty (tuple21 (set1 int) b))) (infix_plmngt b (set1 int) (t2tb s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set (set Int))) (x Int) (y (set Int)))
  (=> (and (mem1 x s) (mem2 y t)) (mem (set1 (tuple21 int (set1 int)))
  (add (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y))
  (empty (tuple21 int (set1 int))))
  (infix_plmngt (set1 int) int (t2tb1 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y))
  (empty (tuple21 int int))) (infix_plmngt int int (t2tb1 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (x Int) (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb2 x) y) (empty (tuple21 int b)))
  (infix_plmngt b int (t2tb1 s) t))))))

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
  (forall ((x uni) (y (set Int))) (! (mem (set1 (tuple21 a (set1 int)))
  (add (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y))
  (empty (tuple21 a (set1 int))))
  (infix_mnmngt (set1 int) a (add a x (empty a))
  (add (set1 int) (t2tb1 y) (t2tb empty2)))) :pattern ((add
                                                       (tuple21 a (set1 int))
                                                       (Tuple2 a (set1 int) x
                                                       (t2tb1 y))
                                                       (empty
                                                       (tuple21 a (set1 int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Int)) (! (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb2 y)) (empty (tuple21 a int)))
  (infix_mnmngt int a (add a x (empty a)) (add int (t2tb2 y) (t2tb1 empty1)))) :pattern (
  (add (tuple21 a int) (Tuple2 a int x (t2tb2 y)) (empty (tuple21 a int)))) ))))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (set Int))) (! (mem
  (set1 (tuple21 (set1 int) (set1 int)))
  (add (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y))
  (empty (tuple21 (set1 int) (set1 int))))
  (infix_mnmngt (set1 int) (set1 int)
  (add (set1 int) (t2tb1 x) (t2tb empty2))
  (add (set1 int) (t2tb1 y) (t2tb empty2)))) :pattern ((tb2t7
                                                       (add
                                                       (tuple21 (set1 int)
                                                       (set1 int))
                                                       (Tuple2 (set1 int)
                                                       (set1 int) (t2tb1 x)
                                                       (t2tb1 y))
                                                       (empty
                                                       (tuple21 (set1 int)
                                                       (set1 int)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y Int)) (! (mem (set1 (tuple21 (set1 int) int))
  (add (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y))
  (empty (tuple21 (set1 int) int)))
  (infix_mnmngt int (set1 int) (add (set1 int) (t2tb1 x) (t2tb empty2))
  (add int (t2tb2 y) (t2tb1 empty1)))) :pattern ((tb2t10
                                                 (add
                                                 (tuple21 (set1 int) int)
                                                 (Tuple2 (set1 int) int
                                                 (t2tb1 x) (t2tb2 y))
                                                 (empty
                                                 (tuple21 (set1 int) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (set Int)) (y uni)) (! (mem (set1 (tuple21 (set1 int) b))
  (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y)
  (empty (tuple21 (set1 int) b)))
  (infix_mnmngt b (set1 int) (add (set1 int) (t2tb1 x) (t2tb empty2))
  (add b y (empty b)))) :pattern ((add (tuple21 (set1 int) b)
                                  (Tuple2 (set1 int) b (t2tb1 x) y)
                                  (empty (tuple21 (set1 int) b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (set Int))) (! (mem (set1 (tuple21 int (set1 int)))
  (add (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y))
  (empty (tuple21 int (set1 int))))
  (infix_mnmngt (set1 int) int (add int (t2tb2 x) (t2tb1 empty1))
  (add (set1 int) (t2tb1 y) (t2tb empty2)))) :pattern ((tb2t13
                                                       (add
                                                       (tuple21 int
                                                       (set1 int))
                                                       (Tuple2 int (set1 int)
                                                       (t2tb2 x) (t2tb1 y))
                                                       (empty
                                                       (tuple21 int
                                                       (set1 int)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y))
  (empty (tuple21 int int)))
  (infix_mnmngt int int (add int (t2tb2 x) (t2tb1 empty1))
  (add int (t2tb2 y) (t2tb1 empty1)))) :pattern ((tb2t16
                                                 (add (tuple21 int int)
                                                 (Tuple2 int int (t2tb2 x)
                                                 (t2tb2 y))
                                                 (empty (tuple21 int int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni)) (! (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb2 x) y) (empty (tuple21 int b)))
  (infix_mnmngt b int (add int (t2tb2 x) (t2tb1 empty1)) (add b y (empty b)))) :pattern (
  (add (tuple21 int b) (Tuple2 int b (t2tb2 x) y) (empty (tuple21 int b)))) ))))

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
  (forall ((f uni) (s (set (set Int))) (t uni) (a (set Int)))
  (=>
  (and (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb s) t)) (mem2 a
  (tb2t (dom b (set1 int) f)))) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb1 a) (apply b (set1 int) f (t2tb1 a))) f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t)) (mem1
  a (tb2t1 (dom b int f)))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb2 a) (apply b int f (t2tb2 a))) f)))))

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
  (forall ((f uni) (s (set (set Int))) (t uni) (a (set Int)))
  (=>
  (and (mem (set1 (tuple21 (set1 int) b)) f
  (infix_mnmngt b (set1 int) (t2tb s) t)) (mem2 a s)) (mem
  (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb1 a) (apply b (set1 int) f (t2tb1 a))) f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_mnmngt b int (t2tb1 s) t)) (mem1
  a s)) (mem (tuple21 int b)
  (Tuple2 int b (t2tb2 a) (apply b int f (t2tb2 a))) f)))))

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
  (forall ((x uni) (f uni) (s uni) (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 a (set1 int))) f
     (infix_plmngt (set1 int) a s (t2tb t))) (mem a x (dom (set1 int) a f)))
     (mem2 (tb2t1 (apply (set1 int) a f x)) t)) :pattern ((mem
  (set1 (tuple21 a (set1 int))) f (infix_plmngt (set1 int) a s (t2tb t)))
  (tb2t1 (apply (set1 int) a f x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
     (mem a x (dom int a f))) (mem1 (tb2t2 (apply int a f x)) t)) :pattern ((mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (tb2t2 (apply int a f x))) ))))

;; apply_range
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int) (set Int))))
  (s (set (set Int))) (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb7 f)
     (infix_plmngt (set1 int) (set1 int) (t2tb s) (t2tb t))) (mem2 x
     (tb2t (dom (set1 int) (set1 int) (t2tb7 f))))) (mem2
     (tb2t1 (apply (set1 int) (set1 int) (t2tb7 f) (t2tb1 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 int) (set1 int))) (t2tb7 f)
  (infix_plmngt (set1 int) (set1 int) (t2tb s) (t2tb t)))
  (tb2t1 (apply (set1 int) (set1 int) (t2tb7 f) (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int) Int))) (s (set (set Int)))
  (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) int)) (t2tb10 f)
     (infix_plmngt int (set1 int) (t2tb s) (t2tb1 t))) (mem2 x
     (tb2t (dom int (set1 int) (t2tb10 f))))) (mem1
     (tb2t2 (apply int (set1 int) (t2tb10 f) (t2tb1 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 int) int)) (t2tb10 f)
  (infix_plmngt int (set1 int) (t2tb s) (t2tb1 t)))
  (tb2t2 (apply int (set1 int) (t2tb10 f) (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (set Int)) (f uni) (s (set (set Int))) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) b)) f
     (infix_plmngt b (set1 int) (t2tb s) t)) (mem2 x
     (tb2t (dom b (set1 int) f)))) (mem b (apply b (set1 int) f (t2tb1 x))
     t)) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) f (infix_plmngt b (set1 int) (t2tb s) t))
  (apply b (set1 int) f (t2tb1 x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int (set Int)))) (s (set Int))
  (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 int (set1 int))) (t2tb13 f)
     (infix_plmngt (set1 int) int (t2tb1 s) (t2tb t))) (mem1 x
     (tb2t1 (dom (set1 int) int (t2tb13 f))))) (mem2
     (tb2t1 (apply (set1 int) int (t2tb13 f) (t2tb2 x))) t)) :pattern ((mem
  (set1 (tuple21 int (set1 int))) (t2tb13 f)
  (infix_plmngt (set1 int) int (t2tb1 s) (t2tb t)))
  (tb2t1 (apply (set1 int) int (t2tb13 f) (t2tb2 x)))) )))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 int int)) (t2tb16 f)
     (infix_plmngt int int (t2tb1 s) (t2tb1 t))) (mem1 x
     (tb2t1 (dom int int (t2tb16 f))))) (mem1
     (tb2t2 (apply int int (t2tb16 f) (t2tb2 x))) t)) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb16 f)
  (infix_plmngt int int (t2tb1 s) (t2tb1 t)))
  (tb2t2 (apply int int (t2tb16 f) (t2tb2 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x Int) (f uni) (s (set Int)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
     (mem1 x (tb2t1 (dom b int f)))) (mem b (apply b int f (t2tb2 x)) t)) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (apply b int f (t2tb2 x))) ))))

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
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb t) u))
  (and (mem a x (dom (set1 int) a f)) (mem2 (tb2t1 (apply (set1 int) a f x))
  (tb2t (dom c (set1 int) g))))))
  (= (apply c a (semicolon c (set1 int) a f g) x) (apply c (set1 int) g
                                                  (apply (set1 int) a f x)))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb1 t) u))
  (and (mem a x (dom int a f)) (mem1 (tb2t2 (apply int a f x))
  (tb2t1 (dom c int g))))))
  (= (apply c a (semicolon c int a f g) x) (apply c int g (apply int a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set Int)) (f (set (tuple2 (set Int) (set Int)))) (g uni)
  (s (set (set Int))) (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb7 f)
  (infix_plmngt (set1 int) (set1 int) (t2tb s) (t2tb t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb t) u))
  (and (mem2 x (tb2t (dom (set1 int) (set1 int) (t2tb7 f)))) (mem2
  (tb2t1 (apply (set1 int) (set1 int) (t2tb7 f) (t2tb1 x)))
  (tb2t (dom c (set1 int) g))))))
  (= (apply c (set1 int) (semicolon c (set1 int) (set1 int) (t2tb7 f) g)
     (t2tb1 x)) (apply c (set1 int) g
                (apply (set1 int) (set1 int) (t2tb7 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set Int)) (f (set (tuple2 (set Int) Int))) (g uni)
  (s (set (set Int))) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) int)) (t2tb10 f)
  (infix_plmngt int (set1 int) (t2tb s) (t2tb1 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb1 t) u))
  (and (mem2 x (tb2t (dom int (set1 int) (t2tb10 f)))) (mem1
  (tb2t2 (apply int (set1 int) (t2tb10 f) (t2tb1 x))) (tb2t1 (dom c int g))))))
  (= (apply c (set1 int) (semicolon c int (set1 int) (t2tb10 f) g) (t2tb1 x)) 
  (apply c int g (apply int (set1 int) (t2tb10 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (set Int)) (f uni) (g uni) (s (set (set Int))) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem2 x (tb2t (dom b (set1 int) f))) (mem b
  (apply b (set1 int) f (t2tb1 x)) (dom c b g)))))
  (= (apply c (set1 int) (semicolon c b (set1 int) f g) (t2tb1 x)) (apply c b
                                                                   g
                                                                   (apply b
                                                                   (set1 int)
                                                                   f
                                                                   (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int (set Int)))) (g uni) (s (set Int))
  (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 int (set1 int))) (t2tb13 f)
  (infix_plmngt (set1 int) int (t2tb1 s) (t2tb t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb t) u))
  (and (mem1 x (tb2t1 (dom (set1 int) int (t2tb13 f)))) (mem2
  (tb2t1 (apply (set1 int) int (t2tb13 f) (t2tb2 x)))
  (tb2t (dom c (set1 int) g))))))
  (= (apply c int (semicolon c (set1 int) int (t2tb13 f) g) (t2tb2 x)) 
  (apply c (set1 int) g (apply (set1 int) int (t2tb13 f) (t2tb2 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int Int))) (g uni) (s (set Int))
  (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int int)) (t2tb16 f)
  (infix_plmngt int int (t2tb1 s) (t2tb1 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb1 t) u))
  (and (mem1 x (tb2t1 (dom int int (t2tb16 f)))) (mem1
  (tb2t2 (apply int int (t2tb16 f) (t2tb2 x))) (tb2t1 (dom c int g))))))
  (= (apply c int (semicolon c int int (t2tb16 f) g) (t2tb2 x)) (apply c 
                                                                int g
                                                                (apply 
                                                                int int
                                                                (t2tb16 f)
                                                                (t2tb2 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x Int) (f uni) (g uni) (s (set Int)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t1 (dom b int f))) (mem b (apply b int f (t2tb2 x))
  (dom c b g)))))
  (= (apply c int (semicolon c b int f g) (t2tb2 x)) (apply c b g
                                                     (apply b int f
                                                     (t2tb2 x))))))))

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
  (forall ((f uni) (s (set (set Int))) (t uni))
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (infix_gtmngt b (set1 int) (t2tb s) t))
  (=> (mem2 x s)
  (=> (mem2 y s)
  (=> (= (apply b (set1 int) f (t2tb1 x)) (apply b (set1 int) f (t2tb1 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (forall ((x Int) (y Int))
  (=> (mem (set1 (tuple21 int b)) f (infix_gtmngt b int (t2tb1 s) t))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=> (= (apply b int f (t2tb2 x)) (apply b int f (t2tb2 y))) (= x y)))))))))

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
  (forall ((x (set Int)) (y (set Int)) (s (set (set Int))))
  (= (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y))
  (id (set1 int) (t2tb s))) (and (mem2 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y))
  (id int (t2tb1 s))) (and (mem1 x s) (= x y)))))

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
  (= (seq_length a n s) (infix_mnmngt a int (t2tb1 (mk 1 n)) s)))))

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
  (infix_mnmngt a int (t2tb1 (mk 1 (size a r))) s))))))

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
  (forall ((s (set (set Int)))) (is_finite_subset (set1 int) (t2tb empty2)
  (t2tb s) 0)))

;; Empty
  (assert
  (forall ((s (set Int))) (is_finite_subset int (t2tb1 empty1) (t2tb1 s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (=> (is_finite_subset (set1 int) (t2tb s1) (t2tb s2) c)
  (=> (mem2 x s2)
  (=> (mem2 x s1) (is_finite_subset (set1 int)
  (add (set1 int) (t2tb1 x) (t2tb s1)) (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset int (add int (t2tb2 x) (t2tb1 s1))
  (t2tb1 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (=> (is_finite_subset (set1 int) (t2tb s1) (t2tb s2) c)
  (=> (mem2 x s2)
  (=> (not (mem2 x s1)) (is_finite_subset (set1 int)
  (add (set1 int) (t2tb1 x) (t2tb s1)) (t2tb s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset int (add int (t2tb2 x) (t2tb1 s1))
  (t2tb1 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2)
  (=> (not (mem a x s1)) (is_finite_subset a (add a x s1) s2 (+ c 1))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (set Int))) (z1 (set (set Int))) (z2 Int))
  (=> (is_finite_subset (set1 int) (t2tb z) (t2tb z1) z2)
  (or
  (or
  (exists ((s (set (set Int)))) (and (and (= z empty2) (= z1 s)) (= z2 0)))
  (exists ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (and (is_finite_subset (set1 int) (t2tb s1) (t2tb s2) c)
  (and (mem2 x s2)
  (and (mem2 x s1)
  (and (and (= z (tb2t (add (set1 int) (t2tb1 x) (t2tb s1)))) (= z1 s2))
  (= z2 c)))))))
  (exists ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (and (is_finite_subset (set1 int) (t2tb s1) (t2tb s2) c)
  (and (mem2 x s2)
  (and (not (mem2 x s1))
  (and (and (= z (tb2t (add (set1 int) (t2tb1 x) (t2tb s1)))) (= z1 s2))
  (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb1 z) (t2tb1 z1) z2)
  (or
  (or (exists ((s (set Int))) (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1)
  (and (and (= z (tb2t1 (add int (t2tb2 x) (t2tb1 s1)))) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (and (mem1 x s2)
  (and (not (mem1 x s1))
  (and (and (= z (tb2t1 (add int (t2tb2 x) (t2tb1 s1)))) (= z1 s2))
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
  (=> (<= a b) (is_finite_subset int (t2tb1 (mk a b)) (t2tb1 integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb1 (mk a b)) (t2tb1 integer) 0))))

(declare-fun finite_subsets (ty uni) uni)

;; finite_subsets_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (finite_subsets a x)))))

;; finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem2 x (tb2t (finite_subsets int (t2tb1 s))))
  (exists ((c Int)) (is_finite_subset int (t2tb1 x) (t2tb1 s) c)))))

;; finite_subsets_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((s (set (set Int)))) (mem (set1 (set1 int)) (t2tb empty2)
  (finite_subsets (set1 int) (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((s (set Int))) (mem2 empty1
  (tb2t (finite_subsets int (t2tb1 s))))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))))
  (=> (mem (set1 (set1 int)) (t2tb s1) (finite_subsets (set1 int) (t2tb s2)))
  (=> (mem2 x s2) (mem (set1 (set1 int)) (add (set1 int) (t2tb1 x) (t2tb s1))
  (finite_subsets (set1 int) (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem2 s1 (tb2t (finite_subsets int (t2tb1 s2))))
  (=> (mem1 x s2) (mem2 (tb2t1 (add int (t2tb2 x) (t2tb1 s1)))
  (tb2t (finite_subsets int (t2tb1 s2))))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (=> (mem2 s1 (tb2t (finite_subsets int (t2tb1 s3))))
  (=> (mem2 s2 (tb2t (finite_subsets int (t2tb1 s3)))) (mem2
  (tb2t1 (union int (t2tb1 s1) (t2tb1 s2)))
  (tb2t (finite_subsets int (t2tb1 s3))))))))

;; finite_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))))
  (=> (mem (set1 (set1 int)) (t2tb s1) (finite_subsets (set1 int) (t2tb s2)))
  (or (= s1 empty2)
  (exists ((x (set Int)) (s3 (set (set Int))))
  (and (= s1 (tb2t (add (set1 int) (t2tb1 x) (t2tb s3)))) (mem
  (set1 (set1 int)) (t2tb s3) (finite_subsets (set1 int) (t2tb s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (=> (mem2 s1 (tb2t (finite_subsets int (t2tb1 s2))))
  (or (= s1 empty1)
  (exists ((x Int) (s3 (set Int)))
  (and (= s1 (tb2t1 (add int (t2tb2 x) (t2tb1 s3)))) (mem2 s3
  (tb2t (finite_subsets int (t2tb1 s2))))))))))

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
  (forall ((s (set (set Int))) (x (set (set Int))))
  (= (mem (set1 (set1 int)) (t2tb x)
  (non_empty_finite_subsets (set1 int) (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset (set1 int) (t2tb x) (t2tb s) c) (not (= x empty2)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem2 x (tb2t (non_empty_finite_subsets int (t2tb1 s))))
  (exists ((c Int))
  (and (is_finite_subset int (t2tb1 x) (t2tb1 s) c) (not (= x empty1)))))))

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
  (assert (= (card (set1 int) (t2tb empty2)) 0))

;; card_Empty
  (assert (= (card int (t2tb1 empty1)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))))
  (! (=> (mem (set1 (set1 int)) (t2tb s1)
     (finite_subsets (set1 int) (t2tb s2)))
     (=> (not (mem2 x s1))
     (= (card (set1 int) (add (set1 int) (t2tb1 x) (t2tb s1))) (+ (card
                                                                  (set1 int)
                                                                  (t2tb s1)) 1)))) :pattern ((mem
  (set1 (set1 int)) (t2tb s1) (finite_subsets (set1 int) (t2tb s2)))
  (card (set1 int) (add (set1 int) (t2tb1 x) (t2tb s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem2 s1 (tb2t (finite_subsets int (t2tb1 s2))))
     (=> (not (mem1 x s1))
     (= (card int (add int (t2tb2 x) (t2tb1 s1))) (+ (card int (t2tb1 s1)) 1)))) :pattern ((mem2
  s1 (tb2t (finite_subsets int (t2tb1 s2))))
  (card int (add int (t2tb2 x) (t2tb1 s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))))
  (! (=> (mem (set1 (set1 int)) (t2tb s1)
     (finite_subsets (set1 int) (t2tb s2)))
     (=> (mem2 x s1)
     (= (card (set1 int) (add (set1 int) (t2tb1 x) (t2tb s1))) (card
                                                               (set1 int)
                                                               (t2tb s1))))) :pattern ((mem
  (set1 (set1 int)) (t2tb s1) (finite_subsets (set1 int) (t2tb s2)))
  (card (set1 int) (add (set1 int) (t2tb1 x) (t2tb s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem2 s1 (tb2t (finite_subsets int (t2tb1 s2))))
     (=> (mem1 x s1)
     (= (card int (add int (t2tb2 x) (t2tb1 s1))) (card int (t2tb1 s1))))) :pattern ((mem2
  s1 (tb2t (finite_subsets int (t2tb1 s2))))
  (card int (add int (t2tb2 x) (t2tb1 s1)))) )))

;; card_Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (mem a x s1) (= (card a (add a x s1)) (card a s1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (! (=> (mem2 s1 (tb2t (finite_subsets int (t2tb1 s3))))
     (=> (mem2 s2 (tb2t (finite_subsets int (t2tb1 s3))))
     (=> (is_empty int (inter int (t2tb1 s1) (t2tb1 s2)))
     (= (card int (union int (t2tb1 s1) (t2tb1 s2))) (+ (card int (t2tb1 s1)) 
     (card int (t2tb1 s2))))))) :pattern ((mem2
  s1 (tb2t (finite_subsets int (t2tb1 s3)))) (mem2 s2
  (tb2t (finite_subsets int (t2tb1 s3))))
  (card int (union int (t2tb1 s1) (t2tb1 s2)))) )))

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
  (forall ((a1 uni) (b (set (set Int))) (x uni) (y (set Int)))
  (! (= (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y))
     (times (set1 int) a a1 (t2tb b))) (and (mem a x a1) (mem2 y b))) :pattern ((mem
  (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y))
  (times (set1 int) a a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set Int)) (x uni) (y Int))
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y))
     (times int a a1 (t2tb1 b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb2 y)) (times int a a1 (t2tb1 b)))) ))))

;; times_def
  (assert
  (forall ((a (set (set Int))) (b (set (set Int))) (x (set Int))
  (y (set Int)))
  (! (= (mem (tuple21 (set1 int) (set1 int))
     (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y))
     (times (set1 int) (set1 int) (t2tb a) (t2tb b)))
     (and (mem2 x a) (mem2 y b))) :pattern ((mem
  (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y))
  (times (set1 int) (set1 int) (t2tb a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set (set Int))) (b (set Int)) (x (set Int)) (y Int))
  (! (= (mem (tuple21 (set1 int) int)
     (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y))
     (times int (set1 int) (t2tb a) (t2tb1 b))) (and (mem2 x a) (mem1 y b))) :pattern ((mem
  (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y))
  (times int (set1 int) (t2tb a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (set Int))) (b1 uni) (x (set Int)) (y uni))
  (! (= (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y)
     (times b (set1 int) (t2tb a) b1)) (and (mem2 x a) (mem b y b1))) :pattern ((mem
  (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y)
  (times b (set1 int) (t2tb a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set (set Int))) (x Int) (y (set Int)))
  (! (= (mem (tuple21 int (set1 int))
     (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y))
     (times (set1 int) int (t2tb1 a) (t2tb b))) (and (mem1 x a) (mem2 y b))) :pattern ((mem
  (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y))
  (times (set1 int) int (t2tb1 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set Int)) (x Int) (y Int))
  (! (= (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y))
     (times int int (t2tb1 a) (t2tb1 b))) (and (mem1 x a) (mem1 y b))) :pattern ((mem
  (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y))
  (times int int (t2tb1 a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set Int)) (b1 uni) (x Int) (y uni))
  (! (= (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y)
     (times b int (t2tb1 a) b1)) (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 int b) (Tuple2 int b (t2tb2 x) y) (times b int (t2tb1 a) b1))) ))))

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
  (forall ((r uni) (u uni) (v (set (set Int))))
  (and
  (=> (subset (tuple21 a (set1 int)) r (times (set1 int) a u (t2tb v)))
  (forall ((x uni) (y (set Int)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) r)
  (and (mem a x u) (mem2 y v)))))
  (=>
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb1 y)) r)
  (and (mem a x u) (mem2 y v))))) (subset (tuple21 a (set1 int)) r
  (times (set1 int) a u (t2tb v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set Int)))
  (and
  (=> (subset (tuple21 a int) r (times int a u (t2tb1 v)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) r)
  (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb2 y)) r)
  (and (mem a x u) (mem1 y v))))) (subset (tuple21 a int) r
  (times int a u (t2tb1 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set Int) (set Int)))) (u (set (set Int)))
  (v (set (set Int))))
  (= (subset (tuple21 (set1 int) (set1 int)) (t2tb7 r)
  (times (set1 int) (set1 int) (t2tb u) (t2tb v)))
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb1 x) (t2tb1 y)) (t2tb7 r))
  (and (mem2 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set Int) Int))) (u (set (set Int)))
  (v (set Int)))
  (= (subset (tuple21 (set1 int) int) (t2tb10 r)
  (times int (set1 int) (t2tb u) (t2tb1 v)))
  (forall ((x (set Int)) (y Int))
  (=> (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb1 x) (t2tb2 y)) (t2tb10 r))
  (and (mem2 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (set Int))) (v uni))
  (and
  (=> (subset (tuple21 (set1 int) b) r (times b (set1 int) (t2tb u) v))
  (forall ((x (set Int)) (y uni))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) r)
  (and (mem2 x u) (mem b y v)))))
  (=>
  (forall ((x (set Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y) r)
  (and (mem2 x u) (mem b y v))))) (subset (tuple21 (set1 int) b) r
  (times b (set1 int) (t2tb u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int (set Int)))) (u (set Int))
  (v (set (set Int))))
  (= (subset (tuple21 int (set1 int)) (t2tb13 r)
  (times (set1 int) int (t2tb1 u) (t2tb v)))
  (forall ((x Int) (y (set Int)))
  (=> (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb2 x) (t2tb1 y)) (t2tb13 r))
  (and (mem1 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int Int))) (u (set Int)) (v (set Int)))
  (= (subset (tuple21 int int) (t2tb16 r)
  (times int int (t2tb1 u) (t2tb1 v)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb2 x) (t2tb2 y)) (t2tb16 r))
  (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set Int)) (v uni))
  (and
  (=> (subset (tuple21 int b) r (times b int (t2tb1 u) v))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) r)
  (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) r)
  (and (mem1 x u) (mem b y v))))) (subset (tuple21 int b) r
  (times b int (t2tb1 u) v)))))))

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
  (forall ((s uni) (x uni) (y (set Int)))
  (! (=> (mem a x s)
     (= (tb2t1
        (apply (set1 int) a
        (times (set1 int) a s (add (set1 int) (t2tb1 y) (t2tb empty2))) x)) y)) :pattern (
  (tb2t1
  (apply (set1 int) a
  (times (set1 int) a s (add (set1 int) (t2tb1 y) (t2tb empty2))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Int))
  (! (=> (mem a x s)
     (= (tb2t2
        (apply int a (times int a s (add int (t2tb2 y) (t2tb1 empty1))) x)) y)) :pattern (
  (tb2t2 (apply int a (times int a s (add int (t2tb2 y) (t2tb1 empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y (set Int)))
  (! (=> (mem2 x s)
     (= (tb2t1
        (apply (set1 int) (set1 int)
        (times (set1 int) (set1 int) (t2tb s)
        (add (set1 int) (t2tb1 y) (t2tb empty2))) (t2tb1 x))) y)) :pattern (
  (tb2t1
  (apply (set1 int) (set1 int)
  (times (set1 int) (set1 int) (t2tb s)
  (add (set1 int) (t2tb1 y) (t2tb empty2))) (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y Int))
  (! (=> (mem2 x s)
     (= (tb2t2
        (apply int (set1 int)
        (times int (set1 int) (t2tb s) (add int (t2tb2 y) (t2tb1 empty1)))
        (t2tb1 x))) y)) :pattern ((tb2t2
                                  (apply int (set1 int)
                                  (times int (set1 int) (t2tb s)
                                  (add int (t2tb2 y) (t2tb1 empty1)))
                                  (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set (set Int))) (x (set Int)) (y uni))
  (! (=> (sort b y)
     (=> (mem2 x s)
     (= (apply b (set1 int) (times b (set1 int) (t2tb s) (add b y (empty b)))
        (t2tb1 x)) y))) :pattern ((apply b (set1 int)
                                  (times b (set1 int) (t2tb s)
                                  (add b y (empty b))) (t2tb1 x))) ))))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (set Int)))
  (! (=> (mem1 x s)
     (= (tb2t1
        (apply (set1 int) int
        (times (set1 int) int (t2tb1 s)
        (add (set1 int) (t2tb1 y) (t2tb empty2))) (t2tb2 x))) y)) :pattern (
  (tb2t1
  (apply (set1 int) int
  (times (set1 int) int (t2tb1 s) (add (set1 int) (t2tb1 y) (t2tb empty2)))
  (t2tb2 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y Int))
  (! (=> (mem1 x s)
     (= (tb2t2
        (apply int int
        (times int int (t2tb1 s) (add int (t2tb2 y) (t2tb1 empty1)))
        (t2tb2 x))) y)) :pattern ((tb2t2
                                  (apply int int
                                  (times int int (t2tb1 s)
                                  (add int (t2tb2 y) (t2tb1 empty1)))
                                  (t2tb2 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (x Int) (y uni))
  (! (=> (sort b y)
     (=> (mem1 x s)
     (= (apply b int (times b int (t2tb1 s) (add b y (empty b))) (t2tb2 x)) y))) :pattern (
  (apply b int (times b int (t2tb1 s) (add b y (empty b))) (t2tb2 x))) ))))

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
  (forall ((x (set Int)) (y uni) (q uni) (r uni))
  (= (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb1 x) y)
  (infix_lspl b (set1 int) q r))
  (ite (mem2 x (tb2t (dom b (set1 int) r))) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb1 x) y) r) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb1 x) y) q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni) (q uni) (r uni))
  (= (mem (tuple21 int b) (Tuple2 int b (t2tb2 x) y) (infix_lspl b int q r))
  (ite (mem1 x (tb2t1 (dom b int r))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb2 x) y) r) (mem (tuple21 int b)
  (Tuple2 int b (t2tb2 x) y) q))))))

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
  (forall ((b ty))
  (forall ((s (set (set Int))) (t uni) (f uni) (g uni) (x (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) b)) f
     (infix_plmngt b (set1 int) (t2tb s) t)) (mem
     (set1 (tuple21 (set1 int) b)) g (infix_plmngt b (set1 int) (t2tb s) t)))
     (=> (mem2 x (tb2t (dom b (set1 int) g)))
     (= (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb1 x)) 
     (apply b (set1 int) g (t2tb1 x))))) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) f (infix_plmngt b (set1 int) (t2tb s) t))
  (mem (set1 (tuple21 (set1 int) b)) g
  (infix_plmngt b (set1 int) (t2tb s) t))
  (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb1 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t)))
     (=> (mem1 x (tb2t1 (dom b int g)))
     (= (apply b int (infix_lspl b int f g) (t2tb2 x)) (apply b int g
                                                       (t2tb2 x))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t)) (mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t))
  (apply b int (infix_lspl b int f g) (t2tb2 x))) ))))

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
  (forall ((s (set (set Int))) (t uni) (f uni) (g uni) (x (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) b)) f
     (infix_plmngt b (set1 int) (t2tb s) t)) (mem
     (set1 (tuple21 (set1 int) b)) g (infix_plmngt b (set1 int) (t2tb s) t)))
     (=> (not (mem2 x (tb2t (dom b (set1 int) g))))
     (=> (mem2 x (tb2t (dom b (set1 int) f)))
     (= (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb1 x)) 
     (apply b (set1 int) f (t2tb1 x)))))) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) f (infix_plmngt b (set1 int) (t2tb s) t))
  (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb1 x))) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) g (infix_plmngt b (set1 int) (t2tb s) t))
  (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb1 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t)))
     (=> (not (mem1 x (tb2t1 (dom b int g))))
     (=> (mem1 x (tb2t1 (dom b int f)))
     (= (apply b int (infix_lspl b int f g) (t2tb2 x)) (apply b int f
                                                       (t2tb2 x)))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (apply b int (infix_lspl b int f g) (t2tb2 x))) :pattern ((mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t))
  (apply b int (infix_lspl b int f g) (t2tb2 x))) ))))

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

(declare-sort enum_aa 0)

(declare-fun enum_aa1 () ty)

(declare-fun E_bb () enum_aa)

(declare-fun E_cc () enum_aa)

(declare-fun E_dd () enum_aa)

(declare-fun E_ee () enum_aa)

(declare-fun E_ff () enum_aa)

(declare-fun E_gg () enum_aa)

(declare-fun E_hh () enum_aa)

(declare-fun E_ii () enum_aa)

(declare-fun match_enum_aa (ty enum_aa uni uni uni uni uni uni uni uni) uni)

;; match_enum_aa_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_aa) (x1 uni) (x2 uni) (x3 uni) (x4 uni) (x5 uni) (x6 uni)
  (x7 uni) (x8 uni)) (sort a (match_enum_aa a x x1 x2 x3 x4 x5 x6 x7 x8)))))

;; match_enum_aa_E_bb
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z) (= (match_enum_aa a E_bb z z1 z2 z3 z4 z5 z6 z7) z)))))

;; match_enum_aa_E_cc
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z1) (= (match_enum_aa a E_cc z z1 z2 z3 z4 z5 z6 z7) z1)))))

;; match_enum_aa_E_dd
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z2) (= (match_enum_aa a E_dd z z1 z2 z3 z4 z5 z6 z7) z2)))))

;; match_enum_aa_E_ee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z3) (= (match_enum_aa a E_ee z z1 z2 z3 z4 z5 z6 z7) z3)))))

;; match_enum_aa_E_ff
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z4) (= (match_enum_aa a E_ff z z1 z2 z3 z4 z5 z6 z7) z4)))))

;; match_enum_aa_E_gg
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z5) (= (match_enum_aa a E_gg z z1 z2 z3 z4 z5 z6 z7) z5)))))

;; match_enum_aa_E_hh
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z6) (= (match_enum_aa a E_hh z z1 z2 z3 z4 z5 z6 z7) z6)))))

;; match_enum_aa_E_ii
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni))
  (=> (sort a z7) (= (match_enum_aa a E_ii z z1 z2 z3 z4 z5 z6 z7) z7)))))

(declare-fun index_enum_aa (enum_aa) Int)

;; index_enum_aa_E_bb
  (assert (= (index_enum_aa E_bb) 0))

;; index_enum_aa_E_cc
  (assert (= (index_enum_aa E_cc) 1))

;; index_enum_aa_E_dd
  (assert (= (index_enum_aa E_dd) 2))

;; index_enum_aa_E_ee
  (assert (= (index_enum_aa E_ee) 3))

;; index_enum_aa_E_ff
  (assert (= (index_enum_aa E_ff) 4))

;; index_enum_aa_E_gg
  (assert (= (index_enum_aa E_gg) 5))

;; index_enum_aa_E_hh
  (assert (= (index_enum_aa E_hh) 6))

;; index_enum_aa_E_ii
  (assert (= (index_enum_aa E_ii) 7))

;; enum_aa_inversion
  (assert
  (forall ((u enum_aa))
  (or
  (or
  (or
  (or (or (or (or (= u E_bb) (= u E_cc)) (= u E_dd)) (= u E_ee)) (= u E_ff))
  (= u E_gg)) (= u E_hh)) (= u E_ii))))

(declare-fun set_enum_aa () (set enum_aa))

(declare-fun t2tb18 ((set enum_aa)) uni)

;; t2tb_sort
  (assert (forall ((x (set enum_aa))) (sort (set1 enum_aa1) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set enum_aa))

;; BridgeL
  (assert
  (forall ((i (set enum_aa)))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_aa1) j) (= (t2tb18 (tb2t18 j)) j)) :pattern (
  (t2tb18 (tb2t18 j))) )))

(declare-fun t2tb19 (enum_aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_aa)) (sort enum_aa1 (t2tb19 x))))

(declare-fun tb2t19 (uni) enum_aa)

;; BridgeL
  (assert
  (forall ((i enum_aa)) (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_aa1 j) (= (t2tb19 (tb2t19 j)) j)) :pattern ((t2tb19
                                                                (tb2t19 j))) )))

;; set_enum_aa_axiom
  (assert
  (forall ((x enum_aa)) (mem enum_aa1 (t2tb19 x) (t2tb18 set_enum_aa))))

(declare-fun f1 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f1_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= v_xx 0) (= v_yy 1)) (mem1 v_zz integer)) (<= 0 v_zz))
  (<= v_zz 2147483647)) (mem1 v_bbaa integer)) (<= 0 v_bbaa))
  (<= v_bbaa 2147483647)) (mem1 v_bbbb integer)) (<= 0 v_bbbb))
  (<= v_bbbb 2147483647)) (mem1 v_bbcc integer)) (<= 0 v_bbcc))
  (<= v_bbcc 2147483647)) (<= 1 v_bbcc)) (<= v_bbcc 254)) (= v_bbcc v_bbaa))
  (mem1 v_bbdd integer)) (<= 0 v_bbdd)) (<= v_bbdd 2147483647))
  (<= 1 v_bbdd)) (<= v_bbdd 254)) (= v_bbdd v_bbaa)) (mem1 v_bbee integer))
  (<= 0 v_bbee)) (<= v_bbee 2147483647)) (<= 1 v_bbee))
  (<= (+ v_bbee 1) 2147483647)) (= v_bbee v_bbbb)) (mem1 v_bbff integer))
  (<= 0 v_bbff)) (<= v_bbff 2147483647)) (<= 2 v_bbff)) (= v_bbff v_zz))
  (<= (+ v_bbff v_bbdd) 253)) (<= (+ (+ v_bbff v_bbcc) v_bbdd) 251)) (mem1
  v_bbgg integer)) (<= 0 v_bbgg)) (<= v_bbgg 2147483647)) (<= 1 v_bbgg))
  (<= (+ v_bbgg 1) 254)) (= v_bbgg v_zz)))))

(declare-fun f2 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f2_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int)) (f2 v_zz v_yy v_xx v_ww v_vv v_uu
  v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee
  v_bbdd v_bbcc v_bbbb v_bbaa)))

(declare-fun f7 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f7_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f7 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (mem1 v_oo integer) (<= 0 v_oo)) (mem2 v_qq (power1 natural)))
  (mem2 v_ss (power1 natural))) (mem2 v_rr (power1 natural))) (mem2 v_pp
  (power1 natural)))
  (forall ((v_nn1 Int))
  (=> (and (and (mem1 v_nn1 integer) (<= 0 v_nn1)) (<= (+ v_oo 1) v_nn1))
  (not (mem1 v_nn1 v_qq)))))
  (forall ((v_nn1 Int))
  (=> (and (and (mem1 v_nn1 integer) (<= 0 v_nn1)) (<= (+ v_oo 1) v_nn1))
  (not (mem1 v_nn1 v_ss)))))
  (forall ((v_nn1 Int))
  (=> (and (and (mem1 v_nn1 integer) (<= 0 v_nn1)) (<= (+ v_oo 1) v_nn1))
  (not (mem1 v_nn1 v_rr)))))
  (forall ((v_nn1 Int))
  (=> (and (and (mem1 v_nn1 integer) (<= 0 v_nn1)) (<= (+ v_oo 1) v_nn1))
  (not (mem1 v_nn1 v_pp))))) (infix_eqeq int
  (inter int (t2tb1 v_ss) (t2tb1 v_qq)) (t2tb1 empty1))) (infix_eqeq 
  int (inter int (t2tb1 v_rr) (t2tb1 v_qq)) (t2tb1 empty1))) (infix_eqeq 
  int (inter int (t2tb1 v_pp) (t2tb1 v_qq)) (t2tb1 empty1))))))

(declare-fun f8 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f8_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f8 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll true)) (= v_mm false)))))

(declare-fun f10 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f10_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f10 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (mem1
  (+ v_oo 1) integer))))

(declare-fun f11 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f11_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f11 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (<= 0 (+ v_oo 1)))))

(declare-fun f12 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f12_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f12 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll true)) (= v_mm false))
  (mem1 v_nn integer)) (<= 0 v_nn)) (<= (+ (+ v_oo 1) 1) v_nn)))))

(declare-fun f14 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f14_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f14 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 v_nn v_qq)))))

(declare-fun f15 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f15_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f15 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (= v_nn (+ v_oo 1))))))

(declare-fun f17 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f17_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f17 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 v_nn v_ss)))))

(declare-fun f19 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f19_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f19 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 v_nn v_rr)))))

(declare-fun f21 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f21_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f21 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 v_nn v_pp)))))

(declare-fun f23 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f23_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f23 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 (+ v_oo 1) v_ss)))))

(declare-fun f25 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f25_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f25 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 (+ v_oo 1) v_rr)))))

(declare-fun f27 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f27_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f27 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (mem1 (+ v_oo 1) v_pp)))))

(declare-fun f28 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f28_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f28 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll false)) (= v_mm false)))))

(declare-fun f29 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f29_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f29 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll false)) (= v_mm false))
  (mem1 v_nn integer)) (<= 0 v_nn)) (<= (+ (+ v_oo 1) 1) v_nn)))))

(declare-fun f30 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f30_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f30 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (infix_eqeq int
  (inter int
  (union int (t2tb1 v_ss) (add int (t2tb2 (+ v_oo 1)) (t2tb1 empty1)))
  (t2tb1 v_qq)) (t2tb1 empty1)))))

(declare-fun f31 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f31_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f31 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll true)) (= v_mm false)))))

(declare-fun f32 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f32_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f32 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll true)) (= v_mm false))
  (mem1 v_nn integer)) (<= 0 v_nn)) (<= (+ (+ v_oo 1) 1) v_nn)))))

(declare-fun f33 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f33_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f33 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (infix_eqeq int
  (inter int
  (union int (t2tb1 v_rr) (add int (t2tb2 (+ v_oo 1)) (t2tb1 empty1)))
  (t2tb1 v_qq)) (t2tb1 empty1)))))

(declare-fun f34 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f34_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f34 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll false))
  (= v_mm false)))))

(declare-fun f35 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f35_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f35 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll false))
  (= v_mm false)) (mem1 v_nn integer)) (<= 0 v_nn))
  (<= (+ (+ v_oo 1) 1) v_nn)))))

(declare-fun f36 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f36_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f36 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (infix_eqeq int
  (inter int
  (union int (t2tb1 v_pp) (add int (t2tb2 (+ v_oo 1)) (t2tb1 empty1)))
  (t2tb1 v_qq)) (t2tb1 empty1)))))

(declare-fun f37 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f37_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f37 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (not
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll true)) (= v_mm false)))
  (not
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll false)) (= v_mm false))))
  (not
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll true)) (= v_mm false))))
  (not
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll false))
  (= v_mm false)))))))

(declare-fun f38 (Int Int Int Bool Bool Bool Bool (set Int) (set Int)
  (set Int) (set Int) Int Int Bool Bool Bool Bool Int Int Int Int Int Int
  Int) Bool)

;; f38_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f38 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll true)) (= v_mm false)))
  (not
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll false)) (= v_mm false))))
  (not
  (and (and (and (= v_jj true) (= v_kk true)) (= v_ll true)) (= v_mm false))))
  (not
  (and (and (and (= v_jj false) (= v_kk true)) (= v_ll false))
  (= v_mm false)))) (mem1 v_nn integer)) (<= 0 v_nn))
  (<= (+ (+ v_oo 1) 1) v_nn)))))

(assert
;; bbhh_1
 ;; File "POwhy_bpo2why/p4/p4_2.why", line 410, characters 7-13
  (not
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Bool) (v_vv Bool)
  (v_uu Bool) (v_tt Bool) (v_ss (set Int)) (v_rr (set Int)) (v_qq (set Int))
  (v_pp (set Int)) (v_oo Int) (v_nn Int) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj Bool) (v_bbgg Int) (v_bbff Int) (v_bbee Int) (v_bbdd Int)
  (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (=>
  (and (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (f2
  v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll
  v_kk v_jj v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)) (mem2 
  empty1 (power1 natural))))))
(check-sat)
