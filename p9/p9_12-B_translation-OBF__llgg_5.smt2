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

(declare-fun infix_eqeq (ty uni uni) Bool)

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
  (assert (forall ((x Int)) (not (mem1 x (tb2t (empty int))))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

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
  (= (mem (set1 (tuple21 int int)) (t2tb5 f)
  (relation int int (t2tb s) (t2tb t)))
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
  (forall ((r uni) (dom uni) (y Int))
  (! (and
     (=> (mem1 y (tb2t (image int a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) r)))
     (mem1 y (tb2t (image int a r dom))))) :pattern ((mem1
  y (tb2t (image int a r dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom (set Int)) (y Int))
  (! (= (mem1 y (tb2t (image int int (t2tb5 r) (t2tb dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int int)
     (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 r))))) :pattern ((mem1
  y (tb2t (image int int (t2tb5 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (y uni))
  (! (= (mem b y (image b int r (t2tb dom)))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int b) (Tuple2 int b (t2tb1 x) y) r)))) :pattern ((mem
  b y (image b int r (t2tb dom)))) ))))

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
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb5 f)
  (infix_plmngt int int (t2tb s) (t2tb t)))
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
  (forall ((f uni) (s uni) (t (set Int)) (x uni) (y Int))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y)) f) (mem1 y t))))))

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
  (forall ((s uni) (t (set Int)) (x uni) (y Int))
  (=> (and (mem a x s) (mem1 y t)) (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
  (empty (tuple21 int int))) (infix_plmngt int int (t2tb s) (t2tb t))))))

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
  (forall ((x uni) (f uni) (s uni) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t))) (mem
     a x (dom int a f))) (mem1 (tb2t1 (apply int a f x)) t)) :pattern ((mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb t)))
  (tb2t1 (apply int a f x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 int int)) (t2tb5 f)
     (infix_plmngt int int (t2tb s) (t2tb t))) (mem1 x
     (tb2t (dom int int (t2tb5 f))))) (mem1
     (tb2t1 (apply int int (t2tb5 f) (t2tb1 x))) t)) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 f)
  (infix_plmngt int int (t2tb s) (t2tb t)))
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
  (forall ((a ty) (b ty) (c ty))
  (forall ((f uni) (g uni) (s uni) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple21 b c)) g (infix_plmngt c b t u))) (mem (set1 (tuple21 a c))
  (semicolon c b a f g) (infix_plmngt c a s u))))))

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
  (forall ((x Int) (f (set (tuple2 Int Int))) (g uni) (s (set Int))
  (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int int)) (t2tb5 f)
  (infix_plmngt int int (t2tb s) (t2tb t)))
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
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
  (id int (t2tb s))) (and (mem1 x s) (= x y)))))

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
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

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
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

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
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

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
  (forall ((a1 uni) (b (set Int)) (x uni) (y Int))
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y))
     (times int a a1 (t2tb b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (times int a a1 (t2tb b)))) ))))

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

(declare-sort enum_OBF__aa 0)

(declare-fun enum_OBF__aa1 () ty)

(declare-fun E_OBF__bb () enum_OBF__aa)

(declare-fun E_OBF__cc () enum_OBF__aa)

(declare-fun E_OBF__dd () enum_OBF__aa)

(declare-fun E_OBF__ee () enum_OBF__aa)

(declare-fun E_OBF__ff () enum_OBF__aa)

(declare-fun E_OBF__gg () enum_OBF__aa)

(declare-fun E_OBF__hh () enum_OBF__aa)

(declare-fun match_enum_OBF__aa (ty enum_OBF__aa uni uni uni uni uni uni
  uni) uni)

;; match_enum_OBF__aa_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_OBF__aa) (x1 uni) (x2 uni) (x3 uni) (x4 uni) (x5 uni)
  (x6 uni) (x7 uni)) (sort a (match_enum_OBF__aa a x x1 x2 x3 x4 x5 x6 x7)))))

;; match_enum_OBF__aa_E_OBF__bb
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z) (= (match_enum_OBF__aa a E_OBF__bb z z1 z2 z3 z4 z5 z6) z)))))

;; match_enum_OBF__aa_E_OBF__cc
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z1)
  (= (match_enum_OBF__aa a E_OBF__cc z z1 z2 z3 z4 z5 z6) z1)))))

;; match_enum_OBF__aa_E_OBF__dd
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z2)
  (= (match_enum_OBF__aa a E_OBF__dd z z1 z2 z3 z4 z5 z6) z2)))))

;; match_enum_OBF__aa_E_OBF__ee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z3)
  (= (match_enum_OBF__aa a E_OBF__ee z z1 z2 z3 z4 z5 z6) z3)))))

;; match_enum_OBF__aa_E_OBF__ff
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z4)
  (= (match_enum_OBF__aa a E_OBF__ff z z1 z2 z3 z4 z5 z6) z4)))))

;; match_enum_OBF__aa_E_OBF__gg
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z5)
  (= (match_enum_OBF__aa a E_OBF__gg z z1 z2 z3 z4 z5 z6) z5)))))

;; match_enum_OBF__aa_E_OBF__hh
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni))
  (=> (sort a z6)
  (= (match_enum_OBF__aa a E_OBF__hh z z1 z2 z3 z4 z5 z6) z6)))))

(declare-fun index_enum_OBF__aa (enum_OBF__aa) Int)

;; index_enum_OBF__aa_E_OBF__bb
  (assert (= (index_enum_OBF__aa E_OBF__bb) 0))

;; index_enum_OBF__aa_E_OBF__cc
  (assert (= (index_enum_OBF__aa E_OBF__cc) 1))

;; index_enum_OBF__aa_E_OBF__dd
  (assert (= (index_enum_OBF__aa E_OBF__dd) 2))

;; index_enum_OBF__aa_E_OBF__ee
  (assert (= (index_enum_OBF__aa E_OBF__ee) 3))

;; index_enum_OBF__aa_E_OBF__ff
  (assert (= (index_enum_OBF__aa E_OBF__ff) 4))

;; index_enum_OBF__aa_E_OBF__gg
  (assert (= (index_enum_OBF__aa E_OBF__gg) 5))

;; index_enum_OBF__aa_E_OBF__hh
  (assert (= (index_enum_OBF__aa E_OBF__hh) 6))

;; enum_OBF__aa_inversion
  (assert
  (forall ((u enum_OBF__aa))
  (or
  (or
  (or
  (or (or (or (= u E_OBF__bb) (= u E_OBF__cc)) (= u E_OBF__dd))
  (= u E_OBF__ee)) (= u E_OBF__ff)) (= u E_OBF__gg)) (= u E_OBF__hh))))

(declare-fun set_enum_OBF__aa () (set enum_OBF__aa))

(declare-fun t2tb8 ((set enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__aa))) (sort (set1 enum_OBF__aa1) (t2tb8 x))))

(declare-fun tb2t8 (uni) (set enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__aa)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__aa1) j) (= (t2tb8 (tb2t8 j)) j)) :pattern (
  (t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 (enum_OBF__aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__aa)) (sort enum_OBF__aa1 (t2tb9 x))))

(declare-fun tb2t9 (uni) enum_OBF__aa)

;; BridgeL
  (assert
  (forall ((i enum_OBF__aa))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__aa1 j) (= (t2tb9 (tb2t9 j)) j)) :pattern ((t2tb9
                                                                   (tb2t9 j))) )))

;; set_enum_OBF__aa_axiom
  (assert
  (forall ((x enum_OBF__aa)) (mem enum_OBF__aa1 (t2tb9 x)
  (t2tb8 set_enum_OBF__aa))))

(declare-sort enum_OBF__ii 0)

(declare-fun enum_OBF__ii1 () ty)

(declare-fun E_OBF__jj () enum_OBF__ii)

(declare-fun E_OBF__kk () enum_OBF__ii)

(declare-fun E_OBF__ll () enum_OBF__ii)

(declare-fun E_OBF__mm () enum_OBF__ii)

(declare-fun E_OBF__nn () enum_OBF__ii)

(declare-fun E_OBF__oo () enum_OBF__ii)

(declare-fun E_OBF__pp () enum_OBF__ii)

(declare-fun E_OBF__qq () enum_OBF__ii)

(declare-fun E_OBF__rr () enum_OBF__ii)

(declare-fun E_OBF__ss () enum_OBF__ii)

(declare-fun match_enum_OBF__ii (ty enum_OBF__ii uni uni uni uni uni uni uni
  uni uni uni) uni)

;; match_enum_OBF__ii_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_OBF__ii) (x1 uni) (x2 uni) (x3 uni) (x4 uni) (x5 uni)
  (x6 uni) (x7 uni) (x8 uni) (x9 uni) (x10 uni)) (sort a
  (match_enum_OBF__ii a x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)))))

;; match_enum_OBF__ii_E_OBF__jj
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z)
  (= (match_enum_OBF__ii a E_OBF__jj z z1 z2 z3 z4 z5 z6 z7 z8 z9) z)))))

;; match_enum_OBF__ii_E_OBF__kk
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z1)
  (= (match_enum_OBF__ii a E_OBF__kk z z1 z2 z3 z4 z5 z6 z7 z8 z9) z1)))))

;; match_enum_OBF__ii_E_OBF__ll
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z2)
  (= (match_enum_OBF__ii a E_OBF__ll z z1 z2 z3 z4 z5 z6 z7 z8 z9) z2)))))

;; match_enum_OBF__ii_E_OBF__mm
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z3)
  (= (match_enum_OBF__ii a E_OBF__mm z z1 z2 z3 z4 z5 z6 z7 z8 z9) z3)))))

;; match_enum_OBF__ii_E_OBF__nn
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z4)
  (= (match_enum_OBF__ii a E_OBF__nn z z1 z2 z3 z4 z5 z6 z7 z8 z9) z4)))))

;; match_enum_OBF__ii_E_OBF__oo
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z5)
  (= (match_enum_OBF__ii a E_OBF__oo z z1 z2 z3 z4 z5 z6 z7 z8 z9) z5)))))

;; match_enum_OBF__ii_E_OBF__pp
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z6)
  (= (match_enum_OBF__ii a E_OBF__pp z z1 z2 z3 z4 z5 z6 z7 z8 z9) z6)))))

;; match_enum_OBF__ii_E_OBF__qq
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z7)
  (= (match_enum_OBF__ii a E_OBF__qq z z1 z2 z3 z4 z5 z6 z7 z8 z9) z7)))))

;; match_enum_OBF__ii_E_OBF__rr
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z8)
  (= (match_enum_OBF__ii a E_OBF__rr z z1 z2 z3 z4 z5 z6 z7 z8 z9) z8)))))

;; match_enum_OBF__ii_E_OBF__ss
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni))
  (=> (sort a z9)
  (= (match_enum_OBF__ii a E_OBF__ss z z1 z2 z3 z4 z5 z6 z7 z8 z9) z9)))))

(declare-fun index_enum_OBF__ii (enum_OBF__ii) Int)

;; index_enum_OBF__ii_E_OBF__jj
  (assert (= (index_enum_OBF__ii E_OBF__jj) 0))

;; index_enum_OBF__ii_E_OBF__kk
  (assert (= (index_enum_OBF__ii E_OBF__kk) 1))

;; index_enum_OBF__ii_E_OBF__ll
  (assert (= (index_enum_OBF__ii E_OBF__ll) 2))

;; index_enum_OBF__ii_E_OBF__mm
  (assert (= (index_enum_OBF__ii E_OBF__mm) 3))

;; index_enum_OBF__ii_E_OBF__nn
  (assert (= (index_enum_OBF__ii E_OBF__nn) 4))

;; index_enum_OBF__ii_E_OBF__oo
  (assert (= (index_enum_OBF__ii E_OBF__oo) 5))

;; index_enum_OBF__ii_E_OBF__pp
  (assert (= (index_enum_OBF__ii E_OBF__pp) 6))

;; index_enum_OBF__ii_E_OBF__qq
  (assert (= (index_enum_OBF__ii E_OBF__qq) 7))

;; index_enum_OBF__ii_E_OBF__rr
  (assert (= (index_enum_OBF__ii E_OBF__rr) 8))

;; index_enum_OBF__ii_E_OBF__ss
  (assert (= (index_enum_OBF__ii E_OBF__ss) 9))

;; enum_OBF__ii_inversion
  (assert
  (forall ((u enum_OBF__ii))
  (or
  (or
  (or
  (or
  (or
  (or
  (or (or (or (= u E_OBF__jj) (= u E_OBF__kk)) (= u E_OBF__ll))
  (= u E_OBF__mm)) (= u E_OBF__nn)) (= u E_OBF__oo)) (= u E_OBF__pp))
  (= u E_OBF__qq)) (= u E_OBF__rr)) (= u E_OBF__ss))))

(declare-fun set_enum_OBF__ii () (set enum_OBF__ii))

(declare-fun t2tb10 ((set enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__ii))) (sort (set1 enum_OBF__ii1) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__ii)))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__ii1) j) (= (t2tb10 (tb2t10 j)) j)) :pattern (
  (t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 (enum_OBF__ii) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__ii)) (sort enum_OBF__ii1 (t2tb11 x))))

(declare-fun tb2t11 (uni) enum_OBF__ii)

;; BridgeL
  (assert
  (forall ((i enum_OBF__ii))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__ii1 j) (= (t2tb11 (tb2t11 j)) j)) :pattern (
  (t2tb11 (tb2t11 j))) )))

;; set_enum_OBF__ii_axiom
  (assert
  (forall ((x enum_OBF__ii)) (mem enum_OBF__ii1 (t2tb11 x)
  (t2tb10 set_enum_OBF__ii))))

(declare-fun f1 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

(declare-fun t2tb12 ((set (set (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) int))) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (set (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb13 x))))

(declare-fun tb2t13 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb13 (tb2t13 j)) j) :pattern ((t2tb13 (tb2t13 j))) )))

(declare-fun t2tb14 ((set (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

(declare-fun t2tb15 ((set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

(declare-fun t2tb16 ((set (tuple2 Int Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Bool)))) (sort (set1 (tuple21 int bool))
  (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (tuple2 Int Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Bool))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb16 (tb2t16 j)) j) :pattern ((t2tb16 (tb2t16 j))) )))

(declare-fun t2tb17 ((set (tuple2 Bool Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Int)))) (sort (set1 (tuple21 bool int))
  (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (tuple2 Bool Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Int))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

(declare-fun t2tb18 ((set (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))) (sort
  (set1 (tuple21 (tuple21 int int) int)) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb18 (tb2t18 j)) j) :pattern ((t2tb18 (tb2t18 j))) )))

(declare-fun t2tb19 ((set (set (tuple2 Int Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Bool))))) (sort
  (set1 (set1 (tuple21 int bool))) (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (set (tuple2 Int Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Bool)))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

(declare-fun t2tb20 ((set (tuple2 Int (tuple2 Int (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int (tuple2 Int Int)))))) (sort
  (set1 (tuple21 int (tuple21 int (tuple21 int int)))) (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (tuple2 Int (tuple2 Int (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int (tuple2 Int Int))))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

(declare-fun t2tb21 ((set (tuple2 Int (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int Int))))) (sort
  (set1 (tuple21 int (tuple21 int int))) (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (tuple2 Int (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int Int)))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb21 (tb2t21 j)) j) :pattern ((t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb22 x))))

(declare-fun tb2t22 (uni) (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb22 (tb2t22 j)) j) :pattern ((t2tb22 (tb2t22 j))) )))

(declare-fun t2tb23 ((set (tuple2 Int enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int enum_OBF__aa)))) (sort
  (set1 (tuple21 int enum_OBF__aa1)) (t2tb23 x))))

(declare-fun tb2t23 (uni) (set (tuple2 Int enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int enum_OBF__aa))))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb23 (tb2t23 j)) j) :pattern ((t2tb23 (tb2t23 j))) )))

;; f1_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f1 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
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
  (and (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__wwcc)
  (relation int int (t2tb v_OBF__xxbb) (t2tb v_OBF__xxbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__xxcc)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__xxbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ggcc)
  (relation int int (t2tb v_OBF__xxbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__aacc)
  (relation int int (t2tb v_OBF__xxbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__zzcc)
  (relation int int (t2tb v_OBF__xxbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ccdd)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__eedd)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__rrcc)
  (semicolon int int int (t2tb5 v_OBF__xxcc) (t2tb5 v_OBF__zzcc))))
  (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb5 v_OBF__llcc)
  (inverse int int (t2tb5 v_OBF__llcc)))
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int))
  (inter (tuple21 int int) (t2tb5 v_OBF__wwcc)
  (inverse int int (t2tb5 v_OBF__wwcc)))
  (power (tuple21 int int) (id int (t2tb v_OBF__xxbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__xxcc)
  (infix_plmngt int int (t2tb v_OBF__bbcc) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__xxcc)) (t2tb v_OBF__bbcc))) (infix_eqeq 
  int (ran int int (t2tb5 v_OBF__xxcc)) (t2tb v_OBF__xxbb))) (mem
  (set1 (tuple21 int int))
  (semicolon int int int
  (semicolon int int int (inverse int int (t2tb5 v_OBF__xxcc))
  (t2tb5 v_OBF__llcc)) (t2tb5 v_OBF__xxcc))
  (power (tuple21 int int) (t2tb5 v_OBF__wwcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ggcc)
  (infix_plmngt int int (t2tb v_OBF__xxbb) (t2tb v_OBF__bbcc)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__ggcc)) (t2tb v_OBF__xxbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ggcc)
  (power (tuple21 int int) (inverse int int (t2tb5 v_OBF__xxcc))))) (mem
  (set1 (tuple21 int int))
  (ran (tuple21 int int) int
  (direct_product int int int (t2tb5 v_OBF__ggcc)
  (inverse int int (t2tb5 v_OBF__xxcc))))
  (power (tuple21 int int) (t2tb5 v_OBF__llcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__aacc)
  (infix_plmngt int int (t2tb v_OBF__xxbb) (t2tb v_OBF__bbcc)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__aacc)) (t2tb v_OBF__xxbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__aacc)
  (power (tuple21 int int) (inverse int int (t2tb5 v_OBF__xxcc))))) (mem
  (set1 (tuple21 int int))
  (ran (tuple21 int int) int
  (direct_product int int int (inverse int int (t2tb5 v_OBF__xxcc))
  (t2tb5 v_OBF__aacc))) (power (tuple21 int int) (t2tb5 v_OBF__llcc))))
  (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__dddd)
  (semicolon int int int (t2tb5 v_OBF__ccdd) (t2tb5 v_OBF__ggcc))))
  (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__ffdd)
  (semicolon int int int (t2tb5 v_OBF__eedd) (t2tb5 v_OBF__aacc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ccdd)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__ccdd)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__eedd)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__eedd)) (t2tb v_OBF__wwbb))) (mem (set1 int)
  (t2tb v_OBF__xxbb) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_OBF__xxbb) (empty int)))) (mem (set1 int)
  (t2tb v_OBF__nnff) (power int (t2tb v_OBF__bbcc)))) (mem (set1 int)
  (t2tb v_OBF__hhcc) (power int (t2tb v_OBF__bbcc)))) (mem (set1 int)
  (t2tb v_OBF__ffcc) (power int (t2tb v_OBF__bbcc)))) (mem (set1 int)
  (t2tb v_OBF__ddcc) (power int (t2tb v_OBF__bbcc)))) (mem (set1 int)
  (t2tb v_OBF__cccc) (power int (t2tb v_OBF__bbcc)))) (mem (set1 int)
  (t2tb v_OBF__zzbb) (power int (t2tb v_OBF__bbcc)))) (mem (set1 int)
  (t2tb v_OBF__uubb) (power int (t2tb v_OBF__bbcc)))) (mem1 v_OBF__ooff
  v_OBF__bbcc)) (infix_eqeq int (t2tb v_OBF__mmbb)
  (union int
  (union int
  (union int
  (union int
  (union int
  (union int (union int (t2tb v_OBF__nnff) (t2tb v_OBF__hhcc))
  (t2tb v_OBF__ffcc)) (t2tb v_OBF__ddcc)) (t2tb v_OBF__cccc))
  (t2tb v_OBF__zzbb)) (t2tb v_OBF__uubb))
  (add int (t2tb1 v_OBF__ooff) (empty int))))) (mem (set1 int)
  (t2tb v_OBF__hhcc)
  (power int (diff int (t2tb v_OBF__mmbb) (t2tb v_OBF__nnff))))) (mem
  (set1 int) (t2tb v_OBF__ffcc)
  (power int
  (diff int (t2tb v_OBF__mmbb)
  (union int (t2tb v_OBF__nnff) (t2tb v_OBF__hhcc)))))) (mem (set1 int)
  (t2tb v_OBF__ddcc)
  (power int
  (diff int (t2tb v_OBF__mmbb)
  (union int (union int (t2tb v_OBF__nnff) (t2tb v_OBF__hhcc))
  (t2tb v_OBF__ffcc)))))) (mem (set1 int) (t2tb v_OBF__cccc)
  (power int
  (diff int (t2tb v_OBF__mmbb)
  (union int
  (union int (union int (t2tb v_OBF__nnff) (t2tb v_OBF__hhcc))
  (t2tb v_OBF__ffcc)) (t2tb v_OBF__ddcc)))))) (mem (set1 int)
  (t2tb v_OBF__zzbb)
  (power int
  (diff int (t2tb v_OBF__mmbb)
  (union int
  (union int
  (union int (union int (t2tb v_OBF__nnff) (t2tb v_OBF__hhcc))
  (t2tb v_OBF__ffcc)) (t2tb v_OBF__ddcc)) (t2tb v_OBF__cccc)))))) (mem
  (set1 int) (t2tb v_OBF__uubb)
  (power int
  (diff int (t2tb v_OBF__mmbb)
  (union int
  (union int
  (union int
  (union int (union int (t2tb v_OBF__nnff) (t2tb v_OBF__hhcc))
  (t2tb v_OBF__ffcc)) (t2tb v_OBF__ddcc)) (t2tb v_OBF__cccc))
  (t2tb v_OBF__zzbb)))))) (mem1 v_OBF__ooff v_OBF__mmbb))
  (not (mem1 v_OBF__ooff v_OBF__nnff))) (not (mem1 v_OBF__ooff v_OBF__hhcc)))
  (not (mem1 v_OBF__ooff v_OBF__ffcc))) (not (mem1 v_OBF__ooff v_OBF__ddcc)))
  (not (mem1 v_OBF__ooff v_OBF__cccc))) (not (mem1 v_OBF__ooff v_OBF__zzbb)))
  (not (mem1 v_OBF__ooff v_OBF__uubb))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__llcc)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__rrcc)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__dddd)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ffdd)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int bool)) (t2tb16 v_OBF__ppff)
  (relation bool int (t2tb v_OBF__wwbb) (t2tb3 b_bool)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__rrcc)
  (power (tuple21 int int) (t2tb5 v_OBF__llcc)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__qqff)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__dddd) (t2tb5 v_OBF__llcc))
  (semicolon int int int (t2tb5 v_OBF__ffdd)
  (inverse int int (t2tb5 v_OBF__llcc)))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__rrff)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__dddd) (t2tb5 v_OBF__rrcc))
  (semicolon int int int (t2tb5 v_OBF__ffdd)
  (inverse int int (t2tb5 v_OBF__llcc)))))) (infix_eqeq int
  (t2tb v_OBF__ssff)
  (image int bool (inverse bool int (t2tb16 v_OBF__ppff))
  (add bool (t2tb2 true) (empty bool))))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__dddd)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__dddd)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ffdd)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__ffdd)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int bool)) (t2tb16 v_OBF__ppff)
  (infix_plmngt bool int (t2tb v_OBF__wwbb) (t2tb3 b_bool)))) (infix_eqeq 
  int (dom bool int (t2tb16 v_OBF__ppff)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__qqff)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__rrff)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ttff)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__uuff)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__kkdd)))) (mem (set1 int)
  (t2tb v_OBF__ssff) (power int (t2tb v_OBF__wwbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__vvff)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__ssff)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__uuff)
  (direct_product int int int (t2tb5 v_OBF__qqff) (t2tb5 v_OBF__ttff)))))
  (add int (t2tb1 v_OBF__ggbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__wwff)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__ssff)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__uuff)
  (direct_product int int int (t2tb5 v_OBF__qqff) (t2tb5 v_OBF__ttff)))))
  (add int (t2tb1 v_OBF__hhbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__ooee)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__ssff)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__uuff)
  (direct_product int int int (t2tb5 v_OBF__qqff) (t2tb5 v_OBF__ttff)))))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__nnee)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__ssff)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__uuff)
  (direct_product int int int (t2tb5 v_OBF__rrff) (t2tb5 v_OBF__ttff)))))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__rrff) (power (tuple21 int int) (t2tb5 v_OBF__qqff)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ttff)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__ttff)) (t2tb v_OBF__wwbb))) (mem (set1 int)
  (ran int int (t2tb5 v_OBF__uuff))
  (power int
  (union int
  (union int (add int (t2tb1 v_OBF__ggbb) (empty int))
  (add int (t2tb1 v_OBF__hhbb) (empty int)))
  (add int (t2tb1 v_OBF__ffbb) (empty int)))))) (mem (set1 int)
  (t2tb v_OBF__wwbb) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_OBF__wwbb) (empty int)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ooee)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__nnee)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))) (mem (set1 int)
  (t2tb v_OBF__ppee) (power int (t2tb v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__xxff)
  (times int int
  (diff int (dom int int (t2tb5 v_OBF__ooee))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb5 v_OBF__ooee) (t2tb5 v_OBF__ooee))
  (id int (t2tb v_OBF__bbbb))))) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__nnee)
  (power (tuple21 int int) (t2tb5 v_OBF__ooee)))) (mem1 v_OBF__ppcc
  v_OBF__bbbb)) (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__vvff)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__wwff)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))))
  (not (= v_OBF__ppcc v_OBF__ssbb))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__yyff)
  (union (tuple21 int int) (t2tb5 v_OBF__vvff)
  (semicolon int int int (t2tb5 v_OBF__vvff)
  (times int int (add int (t2tb1 v_OBF__ppcc) (empty int))
  (t2tb v_OBF__bbbb)))))) (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__zzff)
  (union (tuple21 int int) (t2tb5 v_OBF__wwff)
  (semicolon int int int (t2tb5 v_OBF__wwff)
  (times int int (add int (t2tb1 v_OBF__ppcc) (empty int))
  (t2tb v_OBF__bbbb)))))) (mem1 v_OBF__llbb v_OBF__wwdd)) (mem1 v_OBF__ssbb
  v_OBF__bbbb)) (mem (set1 int) (t2tb v_OBF__uu)
  (power int (t2tb v_OBF__bbcc)))) (mem (set1 int) (t2tb v_OBF__iibb)
  (power int (t2tb v_OBF__bbcc)))) (mem (set1 int) (t2tb v_OBF__mmbb)
  (power int (t2tb v_OBF__bbcc)))) (mem (set1 int) (t2tb v_OBF__nnbb)
  (power int (t2tb v_OBF__bbcc)))) (mem1 v_OBF__oobb v_OBF__bbcc)) (mem1
  v_OBF__ppbb v_OBF__bbcc)) (mem1 v_OBF__qqbb v_OBF__bbcc)) (mem1 v_OBF__rrbb
  v_OBF__bbcc)) (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__yyff)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__zzff)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__xxff)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem (set1 int)
  (t2tb v_OBF__aagg) (power int (t2tb v_OBF__bbbb)))) (mem (set1 int)
  (t2tb v_OBF__iibb) (power int (t2tb v_OBF__uu)))) (mem (set1 int)
  (t2tb v_OBF__mmbb)
  (power int (diff int (t2tb v_OBF__bbcc) (t2tb v_OBF__uu))))) (mem
  (set1 int) (t2tb v_OBF__nnbb)
  (power int
  (diff int (t2tb v_OBF__bbcc)
  (union int (t2tb v_OBF__uu) (t2tb v_OBF__mmbb))))))
  (not (mem1 v_OBF__oobb v_OBF__uu))) (not (mem1 v_OBF__oobb v_OBF__mmbb)))
  (not (mem1 v_OBF__oobb v_OBF__nnbb))) (not (= v_OBF__oobb v_OBF__ppbb)))
  (not (= v_OBF__oobb v_OBF__qqbb))) (not (= v_OBF__oobb v_OBF__rrbb)))
  (not (mem1 v_OBF__ppbb v_OBF__uu))) (not (mem1 v_OBF__ppbb v_OBF__mmbb)))
  (not (mem1 v_OBF__ppbb v_OBF__nnbb))) (not (= v_OBF__ppbb v_OBF__oobb)))
  (not (= v_OBF__ppbb v_OBF__qqbb))) (not (= v_OBF__ppbb v_OBF__rrbb)))
  (not (mem1 v_OBF__qqbb v_OBF__uu))) (not (mem1 v_OBF__qqbb v_OBF__mmbb)))
  (not (mem1 v_OBF__qqbb v_OBF__nnbb))) (not (= v_OBF__qqbb v_OBF__oobb)))
  (not (= v_OBF__qqbb v_OBF__ppbb))) (not (= v_OBF__qqbb v_OBF__rrbb)))
  (not (mem1 v_OBF__rrbb v_OBF__uu))) (not (mem1 v_OBF__rrbb v_OBF__mmbb)))
  (not (mem1 v_OBF__rrbb v_OBF__nnbb))) (not (= v_OBF__rrbb v_OBF__oobb)))
  (not (= v_OBF__rrbb v_OBF__ppbb))) (not (= v_OBF__rrbb v_OBF__qqbb)))
  (infix_eqeq int (t2tb v_OBF__bbcc)
  (union int
  (union int (union int (t2tb v_OBF__uu) (t2tb v_OBF__mmbb))
  (t2tb v_OBF__nnbb))
  (union int
  (union int
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int)))
  (add int (t2tb1 v_OBF__qqbb) (empty int)))
  (add int (t2tb1 v_OBF__rrbb) (empty int)))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__bbgg)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb v_OBF__uu) (t2tb5 v_OBF__yyff))
  (times int int (t2tb v_OBF__nnbb) (t2tb v_OBF__aagg)))
  (times int int
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int))) (t2tb v_OBF__aagg)))
  (times int int (t2tb v_OBF__mmbb)
  (add int (t2tb1 v_OBF__ssbb) (empty int))))
  (times int int (t2tb v_OBF__iibb) (t2tb v_OBF__bbbb)))
  (times int int (add int (t2tb1 v_OBF__qqbb) (empty int))
  (t2tb v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__rrbb) (t2tb1 v_OBF__ssbb))
  (empty (tuple21 int int)))))) (infix_eqeq (tuple21 (tuple21 int int) int)
  (t2tb18 v_OBF__ccgg)
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb v_OBF__uu) (t2tb5 v_OBF__zzff))
  (times int int (t2tb v_OBF__nnbb) (t2tb v_OBF__aagg)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__rrbb) (t2tb1 v_OBF__ssbb))
  (empty (tuple21 int int)))) (t2tb v_OBF__wwdd))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int))) (t2tb v_OBF__aagg))
  (add int (t2tb1 v_OBF__llbb) (empty int)))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__ddgg)
  (domain_restriction int int (t2tb v_OBF__uu) (t2tb5 v_OBF__xxff)))) (mem1
  v_OBF__ddee integer)) (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__eegg)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__ffgg)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))) (<= 1 v_OBF__ddee))
  (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb14 v_OBF__gggg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb integer) (t2tb8 set_enum_OBF__aa))
  (t2tb integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb14 v_OBF__hhgg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb integer) (t2tb8 set_enum_OBF__aa))
  (t2tb integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb14 v_OBF__iigg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb integer) (t2tb8 set_enum_OBF__aa))
  (t2tb integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb14 v_OBF__jjgg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb integer) (t2tb8 set_enum_OBF__aa))
  (t2tb integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb14 v_OBF__hhee)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb integer) (t2tb8 set_enum_OBF__aa))
  (t2tb integer))))) (infix_eqeq (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb14 v_OBF__gggg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb1 0) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb9 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb9 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__cc) (empty enum_OBF__aa1))))
  (add int (t2tb1 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb14 v_OBF__hhgg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb1 0) (empty int))
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb9 E_OBF__hh) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb9 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb1 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb14 v_OBF__iigg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb1 1) (empty int))
  (add enum_OBF__aa1 (t2tb9 E_OBF__cc) (empty enum_OBF__aa1)))
  (add int (t2tb1 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb14 v_OBF__jjgg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb1 1) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb9 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb9 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__hh) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb9 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb1 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb14 v_OBF__hhee)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb14 v_OBF__gggg)
  (t2tb14 v_OBF__hhgg)) (t2tb14 v_OBF__iigg)) (t2tb14 v_OBF__jjgg)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__bbgg)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb18 v_OBF__ccgg)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)) (t2tb v_OBF__wwdd)))))
  (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__ddgg)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__eegg)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ffgg)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb15 v_OBF__kkgg)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__bbgg) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__ggbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb18 v_OBF__ccgg)
  (add int (t2tb1 v_OBF__hhbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__ddgg) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__eegg) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__jjee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__ffgg) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__kkee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__llee) (empty int)))))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb15 v_OBF__kkgg)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)) (t2tb v_OBF__wwdd))
  (t2tb v_OBF__kkdd))))) (mem1 v_OBF__ggbb v_OBF__kkdd)) (mem1 v_OBF__hhbb
  v_OBF__kkdd)) (mem1 v_OBF__ffbb v_OBF__kkdd)) (mem1 v_OBF__jjee
  v_OBF__kkdd)) (mem1 v_OBF__kkee v_OBF__kkdd)) (mem1 v_OBF__llee
  v_OBF__kkdd)) (not (= v_OBF__ggbb v_OBF__hhbb)))
  (not (= v_OBF__ggbb v_OBF__ffbb))) (not (= v_OBF__ggbb v_OBF__jjee)))
  (not (= v_OBF__ggbb v_OBF__kkee))) (not (= v_OBF__ggbb v_OBF__llee)))
  (not (= v_OBF__hhbb v_OBF__ggbb))) (not (= v_OBF__hhbb v_OBF__ffbb)))
  (not (= v_OBF__hhbb v_OBF__jjee))) (not (= v_OBF__hhbb v_OBF__kkee)))
  (not (= v_OBF__hhbb v_OBF__llee))) (not (= v_OBF__ffbb v_OBF__ggbb)))
  (not (= v_OBF__ffbb v_OBF__hhbb))) (not (= v_OBF__ffbb v_OBF__jjee)))
  (not (= v_OBF__ffbb v_OBF__kkee))) (not (= v_OBF__ffbb v_OBF__llee)))
  (not (= v_OBF__jjee v_OBF__ggbb))) (not (= v_OBF__jjee v_OBF__hhbb)))
  (not (= v_OBF__jjee v_OBF__ffbb))) (not (= v_OBF__jjee v_OBF__kkee)))
  (not (= v_OBF__jjee v_OBF__llee))) (not (= v_OBF__kkee v_OBF__ggbb)))
  (not (= v_OBF__kkee v_OBF__hhbb))) (not (= v_OBF__kkee v_OBF__ffbb)))
  (not (= v_OBF__kkee v_OBF__jjee))) (not (= v_OBF__kkee v_OBF__llee)))
  (not (= v_OBF__llee v_OBF__ggbb))) (not (= v_OBF__llee v_OBF__hhbb)))
  (not (= v_OBF__llee v_OBF__ffbb))) (not (= v_OBF__llee v_OBF__jjee)))
  (not (= v_OBF__llee v_OBF__kkee))) (mem (set1 int) (t2tb v_OBF__bbcc)
  (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_OBF__bbcc) (empty int)))) (mem (set1 int)
  (t2tb v_OBF__bbbb) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_OBF__bbbb) (empty int)))) (mem (set1 int)
  (t2tb v_OBF__wwdd) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_OBF__wwdd) (empty int)))) (mem (set1 int)
  (t2tb v_OBF__kkdd) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_OBF__kkdd) (empty int)))))))

(declare-fun f2 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

(declare-fun t2tb24 ((set (set enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set enum_OBF__ii)))) (sort (set1 (set1 enum_OBF__ii1))
  (t2tb24 x))))

(declare-fun tb2t24 (uni) (set (set enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (set enum_OBF__ii))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 enum_OBF__ii1)) j) (= (t2tb24 (tb2t24 j)) j)) :pattern (
  (t2tb24 (tb2t24 j))) )))

(declare-fun t2tb25 ((tuple2 (tuple2 Int enum_OBF__aa) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))) (sort
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb25 x))))

(declare-fun tb2t25 (uni) (tuple2 (tuple2 Int enum_OBF__aa) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb25 (tb2t25 j)) j) :pattern ((t2tb25 (tb2t25 j))) )))

(declare-fun t2tb26 ((set (tuple2 (tuple2 Int Int) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Bool)))) (sort
  (set1 (tuple21 (tuple21 int int) bool)) (t2tb26 x))))

(declare-fun tb2t26 (uni) (set (tuple2 (tuple2 Int Int) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Bool))))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb26 (tb2t26 j)) j) :pattern ((t2tb26 (tb2t26 j))) )))

(declare-fun t2tb27 ((tuple2 Int enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa))) (sort (tuple21 int enum_OBF__aa1)
  (t2tb27 x))))

(declare-fun tb2t27 (uni) (tuple2 Int enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int enum_OBF__aa)))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb27 (tb2t27 j)) j) :pattern ((t2tb27 (tb2t27 j))) )))

(declare-fun t2tb28 ((set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))) (sort
  (set1 (tuple21 (tuple21 int int) (tuple21 int int))) (t2tb28 x))))

(declare-fun tb2t28 (uni) (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))))
  (! (= (tb2t28 (t2tb28 i)) i) :pattern ((t2tb28 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb28 (tb2t28 j)) j) :pattern ((t2tb28 (tb2t28 j))) )))

;; f2_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f2 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
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
  (and
  (and
  (and (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__kkcc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__mmcc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int bool)) (t2tb16 v_OBF__jjcc)
  (relation bool int (t2tb v_OBF__wwbb) (t2tb3 b_bool)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__ggdd)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__kkcc) (t2tb5 v_OBF__llcc))
  (semicolon int int int (t2tb5 v_OBF__mmcc)
  (inverse int int (t2tb5 v_OBF__llcc)))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__hhdd)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__kkcc) (t2tb5 v_OBF__rrcc))
  (semicolon int int int (t2tb5 v_OBF__mmcc)
  (inverse int int (t2tb5 v_OBF__llcc)))))) (infix_eqeq int
  (t2tb v_OBF__iidd)
  (image int bool (inverse bool int (t2tb16 v_OBF__jjcc))
  (add bool (t2tb2 true) (empty bool))))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__kkcc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__kkcc)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__mmcc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__mmcc)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int bool)) (t2tb16 v_OBF__jjcc)
  (infix_plmngt bool int (t2tb v_OBF__wwbb) (t2tb3 b_bool)))) (infix_eqeq 
  int (dom bool int (t2tb16 v_OBF__jjcc)) (t2tb v_OBF__wwbb))) (mem
  (set1 enum_OBF__ii1) (t2tb10 v_OBF__jjdd)
  (power enum_OBF__ii1 (t2tb10 set_enum_OBF__ii)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ggdd)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__hhdd)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__oocc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__nncc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__kkdd)))) (mem (set1 int)
  (t2tb v_OBF__iidd) (power int (t2tb v_OBF__wwbb)))) (mem (set1 int)
  (t2tb v_OBF__jjbb) (power int (t2tb v_OBF__wwbb)))) (mem (set1 int)
  (t2tb v_OBF__lldd) (power int (t2tb v_OBF__wwbb)))) (mem (set1 int)
  (t2tb v_OBF__ww) (power int (t2tb v_OBF__bbbb)))) (mem (set1 int)
  (t2tb v_OBF__zz) (power int (t2tb v_OBF__wwbb)))) (mem (set1 int)
  (t2tb v_OBF__mmdd) (power int (t2tb v_OBF__wwbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__nndd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__iidd)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__nncc)
  (direct_product int int int (t2tb5 v_OBF__ggdd) (t2tb5 v_OBF__oocc)))))
  (add int (t2tb1 v_OBF__ggbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__oodd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__iidd)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__nncc)
  (direct_product int int int (t2tb5 v_OBF__ggdd) (t2tb5 v_OBF__oocc)))))
  (add int (t2tb1 v_OBF__hhbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__ppdd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__iidd)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__nncc)
  (direct_product int int int (t2tb5 v_OBF__ggdd) (t2tb5 v_OBF__oocc)))))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__qqdd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb v_OBF__iidd)
  (direct_product (tuple21 int int) int int (t2tb5 v_OBF__nncc)
  (direct_product int int int (t2tb5 v_OBF__hhdd) (t2tb5 v_OBF__oocc)))))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__hhdd) (power (tuple21 int int) (t2tb5 v_OBF__ggdd)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__oocc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__oocc)) (t2tb v_OBF__wwbb))) (mem (set1 int)
  (ran int int (t2tb5 v_OBF__nncc))
  (power int
  (union int
  (union int (add int (t2tb1 v_OBF__ggbb) (empty int))
  (add int (t2tb1 v_OBF__hhbb) (empty int)))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb v_OBF__jjbb)
  (inter int (t2tb v_OBF__iidd)
  (image int int (inverse int int (t2tb5 v_OBF__ggdd))
  (add int (t2tb1 v_OBF__tt) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb v_OBF__lldd)
  (inter int
  (inter int (t2tb v_OBF__iidd)
  (image int int (inverse int int (t2tb5 v_OBF__ggdd))
  (add int (t2tb1 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb5 v_OBF__nncc))
  (add int (t2tb1 v_OBF__eebb) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb v_OBF__ww)
  (image int int (t2tb5 v_OBF__oocc) (t2tb v_OBF__lldd)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb v_OBF__zz)
  (inter int
  (inter int (t2tb v_OBF__iidd)
  (image int int (inverse int int (t2tb5 v_OBF__hhdd))
  (add int (t2tb1 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb5 v_OBF__nncc))
  (add int (t2tb1 v_OBF__eebb) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb v_OBF__mmdd)
  (inter int
  (inter int
  (inter int (t2tb v_OBF__iidd)
  (image int int (inverse int int (t2tb5 v_OBF__ggdd))
  (add int (t2tb1 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb5 v_OBF__nncc))
  (add int (t2tb1 v_OBF__eebb) (empty int))))
  (image int int (inverse int int (t2tb5 v_OBF__oocc))
  (union int (add int (t2tb1 v_OBF__vv) (empty int))
  (add int (t2tb1 v_OBF__ppcc) (empty int)))))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ppdd)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__qqdd)
  (relation int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)))) (mem (set1 int)
  (t2tb v_OBF__yy) (power int (t2tb v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__rrdd)
  (times int int
  (diff int
  (dom int int
  (union (tuple21 int int) (t2tb5 v_OBF__qqdd)
  (range_substraction int int (t2tb5 v_OBF__ppdd)
  (image int int
  (times int int (add int (t2tb1 0) (empty int))
  (diff int (t2tb v_OBF__yy) (add int (t2tb1 v_OBF__vv) (empty int))))
  (add int (t2tb1 v_OBF__xx) (empty int))))))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb5 v_OBF__ppdd) (t2tb5 v_OBF__ppdd))
  (id int (t2tb v_OBF__bbbb))))) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__qqdd)
  (power (tuple21 int int) (t2tb5 v_OBF__ppdd)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__nndd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__oodd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__ssdd)
  (union (tuple21 int int) (t2tb5 v_OBF__nndd)
  (semicolon int int int (t2tb5 v_OBF__nndd)
  (times int int (add int (t2tb1 v_OBF__ppcc) (empty int))
  (t2tb v_OBF__bbbb)))))) (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__ttdd)
  (union (tuple21 int int) (t2tb5 v_OBF__oodd)
  (semicolon int int int (t2tb5 v_OBF__oodd)
  (times int int (add int (t2tb1 v_OBF__ppcc) (empty int))
  (t2tb v_OBF__bbbb)))))) (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__ssdd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ttdd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__rrdd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem (set1 int)
  (t2tb v_OBF__ttbb) (power int (t2tb v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__uudd)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb v_OBF__uu) (t2tb5 v_OBF__ssdd))
  (times int int (t2tb v_OBF__nnbb) (t2tb v_OBF__ttbb)))
  (times int int
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int))) (t2tb v_OBF__ttbb)))
  (times int int (t2tb v_OBF__mmbb)
  (add int (t2tb1 v_OBF__ssbb) (empty int))))
  (dom int (tuple21 int int)
  (range_restriction int (tuple21 int int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__iibb) (t2tb v_OBF__bbbb))
  (add int (t2tb1 1) (empty int))) (add int (t2tb1 v_OBF__xx) (empty int)))))
  (times int int (add int (t2tb1 v_OBF__qqbb) (empty int))
  (t2tb v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__rrbb) (t2tb1 v_OBF__ssbb))
  (empty (tuple21 int int)))))) (infix_eqeq (tuple21 (tuple21 int int) int)
  (t2tb18 v_OBF__vvdd)
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb v_OBF__uu) (t2tb5 v_OBF__ttdd))
  (times int int (t2tb v_OBF__nnbb) (t2tb v_OBF__ttbb)))
  (dom bool (tuple21 int int)
  (range_restriction bool (tuple21 int int)
  (times bool (tuple21 int int)
  (times int int (t2tb v_OBF__mmbb)
  (add int (t2tb1 v_OBF__ssbb) (empty int)))
  (add bool (t2tb2 false) (empty bool)))
  (add bool (t2tb2 v_OBF__yybb) (empty bool)))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__rrbb) (t2tb1 v_OBF__ssbb))
  (empty (tuple21 int int)))) (t2tb v_OBF__wwdd))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int))) (t2tb v_OBF__ttbb))
  (add int (t2tb1 v_OBF__llbb) (empty int)))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__xxdd)
  (domain_restriction int int (t2tb v_OBF__uu) (t2tb5 v_OBF__rrdd)))) (mem1
  v_OBF__yydd v_OBF__bbbb)) (mem1 v_OBF__zzdd integer)) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__aaee)
  (relation int int (t2tb integer) (t2tb v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__bbee)
  (relation int int (t2tb integer) (t2tb v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__ccee)
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 v_OBF__ddee) (t2tb1 0))
  (empty (tuple21 int int))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__zzdd) (t2tb1 v_OBF__xx))
  (empty (tuple21 int int))))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__eeee)
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 0) (t2tb1 0))
  (empty (tuple21 int int))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__zzdd) (t2tb1 v_OBF__xx))
  (empty (tuple21 int int))))))) (mem1 v_OBF__zzdd (mk 0 v_OBF__ddee))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__aaee)
  (infix_plmngt int int (t2tb (mk 1 v_OBF__ddee)) (t2tb v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb5 v_OBF__aaee))
  (t2tb (mk 1 v_OBF__ddee)))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__bbee)
  (infix_plmngt int int (t2tb (mk 1 v_OBF__ddee)) (t2tb v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb5 v_OBF__bbee))
  (t2tb (mk 1 v_OBF__ddee)))) (mem1 v_OBF__ffee integer)) (mem1 v_OBF__xx
  integer)) (mem (tuple21 (tuple21 int enum_OBF__aa1) int)
  (Tuple2 (tuple21 int enum_OBF__aa1) int
  (Tuple2 int enum_OBF__aa1 (t2tb1 v_OBF__ffee) (t2tb9 v_OBF__ggee))
  (t2tb1 v_OBF__xx)) (t2tb14 v_OBF__hhee))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__uudd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb18 v_OBF__vvdd)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)) (t2tb v_OBF__wwdd)))))
  (mem (set1 (tuple21 int int)) (t2tb5 v_OBF__xxdd)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__ccee)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__eeee)
  (power (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb15 v_OBF__iiee)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__uudd) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__ggbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb18 v_OBF__vvdd)
  (add int (t2tb1 v_OBF__hhbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__xxdd) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__ccee) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__jjee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb5 v_OBF__eeee) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__kkee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)) (t2tb v_OBF__wwdd))
  (add int (t2tb1 v_OBF__llee) (empty int)))))) (mem1 v_OBF__ddbb integer))
  (mem1 v_OBF__tt v_OBF__bbcc)) (mem1 v_OBF__vv v_OBF__bbbb)) (mem1
  v_OBF__kkbb v_OBF__wwdd)) (mem1 v_OBF__eebb v_OBF__kkdd)) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb15 v_OBF__iiee)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb v_OBF__bbcc) (t2tb v_OBF__bbbb)) (t2tb v_OBF__wwdd))
  (t2tb v_OBF__kkdd)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb v_OBF__lldd)
  (inter int (t2tb v_OBF__jjbb)
  (image int int (inverse int int (t2tb5 v_OBF__nncc))
  (add int (t2tb1 v_OBF__eebb) (empty int)))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq 
  int (image int int (t2tb5 v_OBF__oocc) (t2tb v_OBF__zz))
  (image int int (t2tb5 v_OBF__qqdd) (add int (t2tb1 v_OBF__tt) (empty int))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq 
  int (t2tb v_OBF__ww)
  (image int int (t2tb5 v_OBF__ppdd) (add int (t2tb1 v_OBF__tt) (empty int))))))
  (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb5 v_OBF__qqdd)
  (range_substraction int int (t2tb5 v_OBF__ppdd)
  (image int int
  (times int int (add int (t2tb1 0) (empty int))
  (diff int (t2tb v_OBF__yy) (add int (t2tb1 v_OBF__vv) (empty int))))
  (add int (t2tb1 1) (empty int))))) (t2tb5 v_OBF__ppdd))) (infix_eqeq
  (tuple21 int int)
  (union (tuple21 int int) (t2tb5 v_OBF__qqdd)
  (range_substraction int int (t2tb5 v_OBF__ppdd)
  (image int int
  (times int int (add int (t2tb1 0) (empty int))
  (diff int (t2tb v_OBF__yy) (add int (t2tb1 v_OBF__vv) (empty int))))
  (add int (t2tb1 0) (empty int)))))
  (union (tuple21 int int) (t2tb5 v_OBF__qqdd)
  (range_substraction int int (t2tb5 v_OBF__ppdd)
  (diff int (t2tb v_OBF__yy) (add int (t2tb1 v_OBF__vv) (empty int)))))))
  (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb5 v_OBF__nnee)
  (range_substraction int int (t2tb5 v_OBF__ooee)
  (image int int
  (times int int (add int (t2tb1 0) (empty int))
  (diff int (t2tb v_OBF__ppee) (add int (t2tb1 v_OBF__ssbb) (empty int))))
  (add int (t2tb1 1) (empty int))))) (t2tb5 v_OBF__ooee))) (mem1 v_OBF__xx
  (tb2t
  (union int (add int (t2tb1 0) (empty int)) (add int (t2tb1 1) (empty int))))))
  (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb14 v_OBF__hhee)
  (infix_plmngt int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int
  (union int (add int (t2tb1 0) (empty int)) (add int (t2tb1 1) (empty int)))
  (t2tb8 set_enum_OBF__aa))
  (union int (add int (t2tb1 0) (empty int)) (add int (t2tb1 1) (empty int))))))
  (infix_eqeq (tuple21 int enum_OBF__aa1)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb14 v_OBF__hhee))
  (times enum_OBF__aa1 int
  (union int (add int (t2tb1 0) (empty int)) (add int (t2tb1 1) (empty int)))
  (t2tb8 set_enum_OBF__aa)))) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__vvcc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__yycc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_OBF__kkcc)
  (semicolon int int int (t2tb5 v_OBF__vvcc) (t2tb5 v_OBF__ggcc))))
  (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__mmcc)
  (semicolon int int int (t2tb5 v_OBF__yycc) (t2tb5 v_OBF__aacc)))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__vvcc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__vvcc)) (t2tb v_OBF__wwbb))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__yycc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__yycc)) (t2tb v_OBF__wwbb)))
  (= v_OBF__qqee v_OBF__ddbb)) (= v_OBF__rree v_OBF__tt))
  (= v_OBF__ssee v_OBF__vv)) (= v_OBF__ttee v_OBF__kkbb))
  (= v_OBF__uuee v_OBF__eebb)) (= v_OBF__vvee v_OBF__mmee))
  (= v_OBF__wwee v_OBF__xx)) (= v_OBF__xxee v_OBF__yydd))
  (= v_OBF__yyee v_OBF__zzdd)) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__zzee) (t2tb5 v_OBF__aaee))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__aaff) (t2tb5 v_OBF__bbee))) (= v_OBF__bbff v_OBF__yybb))
  (infix_eqeq int (t2tb v_OBF__ccff) (t2tb v_OBF__ttbb))) (infix_eqeq 
  int (t2tb v_OBF__ddff) (t2tb v_OBF__yy))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__eeff) (t2tb5 v_OBF__oocc))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__ffff) (t2tb5 v_OBF__nncc))) (infix_eqeq int
  (t2tb v_OBF__ggff) (t2tb v_OBF__jjbb))) (infix_eqeq int (t2tb v_OBF__hhff)
  (t2tb v_OBF__lldd))) (infix_eqeq int (t2tb v_OBF__iiff) (t2tb v_OBF__ww)))
  (infix_eqeq int (t2tb v_OBF__jjff) (t2tb v_OBF__zz))) (infix_eqeq int
  (t2tb v_OBF__kkff) (t2tb v_OBF__mmdd))) (infix_eqeq enum_OBF__ii1
  (t2tb10 v_OBF__llff) (t2tb10 v_OBF__jjdd))) (infix_eqeq (tuple21 int bool)
  (t2tb16 v_OBF__mmff) (t2tb16 v_OBF__jjcc))))))

(declare-fun f8 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f8_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f8 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and (infix_eqeq (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__ggcc) (t2tb5 v_OBF__llcc))
  (semicolon int int int
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__ggcc) (t2tb5 v_OBF__xxcc))
  (t2tb5 v_OBF__wwcc)) (inverse int int (t2tb5 v_OBF__xxcc)))) (infix_eqeq
  (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__aacc)
  (inverse int int (t2tb5 v_OBF__llcc)))
  (semicolon int int int
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__aacc) (t2tb5 v_OBF__xxcc))
  (inverse int int (t2tb5 v_OBF__wwcc)))
  (inverse int int (t2tb5 v_OBF__xxcc))))) (mem1 v_OBF__aadd
  (tb2t (ran int int (t2tb5 v_OBF__ggcc))))))))

(declare-fun f13 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f13_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f13 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and (infix_eqeq (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__ggcc) (t2tb5 v_OBF__llcc))
  (semicolon int int int
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__ggcc) (t2tb5 v_OBF__xxcc))
  (t2tb5 v_OBF__wwcc)) (inverse int int (t2tb5 v_OBF__xxcc)))) (infix_eqeq
  (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__aacc)
  (inverse int int (t2tb5 v_OBF__llcc)))
  (semicolon int int int
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__aacc) (t2tb5 v_OBF__xxcc))
  (inverse int int (t2tb5 v_OBF__wwcc)))
  (inverse int int (t2tb5 v_OBF__xxcc)))))
  (forall ((v_OBF__aadd1 Int))
  (=> (mem1 v_OBF__aadd1 (tb2t (ran int int (t2tb5 v_OBF__ggcc))))
  (and (mem1 v_OBF__aadd1 v_OBF__bbcc)
  (forall ((v_OBF__bbdd1 Int))
  (=>
  (and (mem1 v_OBF__bbdd1 v_OBF__bbcc)
  (= (tb2t1 (apply int int (t2tb5 v_OBF__xxcc) (t2tb1 v_OBF__aadd1))) 
  (tb2t1 (apply int int (t2tb5 v_OBF__xxcc) (t2tb1 v_OBF__bbdd1))))) (mem
  (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__aadd1) (t2tb1 v_OBF__bbdd1))
  (t2tb5 v_OBF__llcc)))))))) (mem1 v_OBF__aadd
  (tb2t (ran int int (t2tb5 v_OBF__aacc))))))))

(declare-fun f35 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f35_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f35 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (infix_eqeq (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__ggcc) (t2tb5 v_OBF__llcc))
  (semicolon int int int
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__ggcc) (t2tb5 v_OBF__xxcc))
  (t2tb5 v_OBF__wwcc)) (inverse int int (t2tb5 v_OBF__xxcc)))) (infix_eqeq
  (tuple21 int int)
  (semicolon int int int (t2tb5 v_OBF__aacc)
  (inverse int int (t2tb5 v_OBF__llcc)))
  (semicolon int int int
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__aacc) (t2tb5 v_OBF__xxcc))
  (inverse int int (t2tb5 v_OBF__wwcc)))
  (inverse int int (t2tb5 v_OBF__xxcc)))))
  (forall ((v_OBF__aadd1 Int))
  (=> (mem1 v_OBF__aadd1 (tb2t (ran int int (t2tb5 v_OBF__ggcc))))
  (and (mem1 v_OBF__aadd1 v_OBF__bbcc)
  (forall ((v_OBF__bbdd1 Int))
  (=>
  (and (mem1 v_OBF__bbdd1 v_OBF__bbcc)
  (= (tb2t1 (apply int int (t2tb5 v_OBF__xxcc) (t2tb1 v_OBF__aadd1))) 
  (tb2t1 (apply int int (t2tb5 v_OBF__xxcc) (t2tb1 v_OBF__bbdd1))))) (mem
  (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__aadd1) (t2tb1 v_OBF__bbdd1))
  (t2tb5 v_OBF__llcc))))))))
  (forall ((v_OBF__aadd1 Int))
  (=> (mem1 v_OBF__aadd1 (tb2t (ran int int (t2tb5 v_OBF__aacc))))
  (and (mem1 v_OBF__aadd1 v_OBF__bbcc)
  (forall ((v_OBF__bbdd1 Int))
  (=>
  (and (mem1 v_OBF__bbdd1 v_OBF__bbcc)
  (= (tb2t1 (apply int int (t2tb5 v_OBF__xxcc) (t2tb1 v_OBF__aadd1))) 
  (tb2t1 (apply int int (t2tb5 v_OBF__xxcc) (t2tb1 v_OBF__bbdd1))))) (mem
  (tuple21 int int)
  (Tuple2 int int (t2tb1 v_OBF__bbdd1) (t2tb1 v_OBF__aadd1))
  (t2tb5 v_OBF__llcc)))))))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_OBF__ccdd)
  (semicolon int int int (t2tb5 v_OBF__dddd) (t2tb5 v_OBF__xxcc))))
  (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__eedd)
  (semicolon int int int (t2tb5 v_OBF__ffdd) (t2tb5 v_OBF__xxcc))))
  (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__vvcc)
  (semicolon int int int (t2tb5 v_OBF__kkcc) (t2tb5 v_OBF__xxcc))))
  (infix_eqeq (tuple21 int int) (t2tb5 v_OBF__yycc)
  (semicolon int int int (t2tb5 v_OBF__mmcc) (t2tb5 v_OBF__xxcc))))
  (infix_eqeq (tuple21 int int)
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__vvcc) (t2tb5 v_OBF__wwcc))
  (inverse int int (t2tb5 v_OBF__xxcc)))
  (semicolon int int int (t2tb5 v_OBF__kkcc) (t2tb5 v_OBF__llcc))))
  (infix_eqeq (tuple21 int int)
  (semicolon int int int
  (semicolon int int int (t2tb5 v_OBF__yycc)
  (inverse int int (t2tb5 v_OBF__wwcc)))
  (inverse int int (t2tb5 v_OBF__xxcc)))
  (semicolon int int int (t2tb5 v_OBF__mmcc)
  (inverse int int (t2tb5 v_OBF__llcc))))))))

(declare-fun f47 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f47_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f47 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__hhcc) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__eecc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__eecc)) (t2tb v_OBF__wwbb)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f49 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f49_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f49 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (mem
  (set1 (tuple21 int int))
  (semicolon int int int (t2tb5 v_OBF__eecc) (t2tb5 v_OBF__ggcc))
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc))))))

(declare-fun f50 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f50_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f50 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (infix_eqeq
  int
  (dom int int
  (semicolon int int int (t2tb5 v_OBF__eecc) (t2tb5 v_OBF__ggcc)))
  (t2tb v_OBF__wwbb)))))

(declare-fun f52 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f52_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f52 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__eecc)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb))))))

(declare-fun f53 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f53_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f53 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__ffcc) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__eecc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__eecc)) (t2tb v_OBF__wwbb)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f54 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f54_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f54 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__ddcc) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__eecc)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__eecc)) (t2tb v_OBF__wwbb)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f55 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f55_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f55 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__cccc) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__vvbb)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__vvbb)) (t2tb v_OBF__wwbb)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f56 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f56_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f56 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (mem
  (set1 (tuple21 int int))
  (semicolon int int int (t2tb5 v_OBF__vvbb) (t2tb5 v_OBF__aacc))
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__bbcc))))))

(declare-fun f57 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f57_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f57 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (infix_eqeq
  int
  (dom int int
  (semicolon int int int (t2tb5 v_OBF__vvbb) (t2tb5 v_OBF__aacc)))
  (t2tb v_OBF__wwbb)))))

(declare-fun f59 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f59_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f59 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (mem
  (set1 (tuple21 int int)) (t2tb5 v_OBF__vvbb)
  (relation int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb))))))

(declare-fun f60 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f60_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f60 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__zzbb) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__vvbb)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__vvbb)) (t2tb v_OBF__wwbb)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f61 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f61_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f61 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__uubb) (mem (set1 (tuple21 int int))
  (t2tb5 v_OBF__vvbb)
  (infix_plmngt int int (t2tb v_OBF__wwbb) (t2tb v_OBF__xxbb)))) (infix_eqeq
  int (dom int int (t2tb5 v_OBF__vvbb)) (t2tb v_OBF__wwbb)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f62 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f62_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f62 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__eebb
  (tb2t
  (union int (add int (t2tb1 v_OBF__ggbb) (empty int))
  (add int (t2tb1 v_OBF__hhbb) (empty int))))) (mem1 v_OBF__tt
  (tb2t
  (union int (union int (t2tb v_OBF__mmbb) (t2tb v_OBF__nnbb))
  (union int
  (union int
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int)))
  (add int (t2tb1 v_OBF__qqbb) (empty int)))
  (add int (t2tb1 v_OBF__rrbb) (empty int)))))))
  (=> (mem1 v_OBF__tt v_OBF__mmbb) (not (= v_OBF__vv v_OBF__ssbb))))
  (=> (mem1 v_OBF__tt v_OBF__nnbb) (not (mem1 v_OBF__vv v_OBF__ttbb))))
  (=>
  (and (mem1 v_OBF__tt
  (tb2t
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int))))) (mem1 v_OBF__vv v_OBF__ttbb))
  (and (= v_OBF__eebb v_OBF__hhbb) (not (= v_OBF__kkbb v_OBF__llbb)))))
  (=> (= v_OBF__tt v_OBF__qqbb) (= v_OBF__eebb v_OBF__hhbb)))
  (=> (= v_OBF__tt v_OBF__rrbb) (not (= v_OBF__vv v_OBF__ssbb))))
  (= v_OBF__ddbb 2)) (mem1 v_OBF__tt
  (tb2t
  (union int (add int (t2tb1 v_OBF__oobb) (empty int))
  (add int (t2tb1 v_OBF__ppbb) (empty int)))))) (mem1 v_OBF__vv v_OBF__ttbb)))))

(declare-fun f64 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f64_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f64 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (not (= v_OBF__kkbb v_OBF__llbb)))))

(declare-fun f67 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f67_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f67 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__eebb
  (tb2t
  (union int
  (union int (add int (t2tb1 v_OBF__ggbb) (empty int))
  (add int (t2tb1 v_OBF__hhbb) (empty int)))
  (add int (t2tb1 v_OBF__ffbb) (empty int))))) (mem1 v_OBF__tt v_OBF__uu))
  (=> (and (= v_OBF__eebb v_OBF__ggbb) (mem1 v_OBF__tt v_OBF__iibb))
  (not (= v_OBF__xx 1)))) (= v_OBF__ddbb 2)) (infix_eqeq int
  (t2tb v_OBF__jjbb) (empty int))) (mem1 v_OBF__tt v_OBF__iibb))
  (= v_OBF__eebb v_OBF__ggbb)))))

(declare-fun f68 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) (set Int) (set (tuple2 Int Int)) Int Int
  (set (tuple2 Int Int)) Bool (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int Int Int (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int
  Bool)) Bool (set Int) (set (tuple2 Int Int)) (set Int) (set enum_OBF__ii)
  Int (set Int) (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set Int) Int (set Int) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set enum_OBF__ii) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set Int) (set Int)
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  enum_OBF__aa (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 (tuple2 Int Int) Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) Bool
  (set (tuple2 Int Int)) Int (set Int) (set Int) (set Int) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) Int) Bool)

;; f68_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (= (f68 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (not (= v_OBF__xx 1)))))

(assert
;; OBF__llgg_5
 ;; File "POwhy_bpo2why/p9/p9_12.why", line 3283, characters 7-18
  (not
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set (tuple2 Int
  Int))) (v_OBF__zzdd Int) (v_OBF__zzcc (set (tuple2 Int Int)))
  (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int
  Int))) (v_OBF__yyee Int) (v_OBF__yydd Int) (v_OBF__yycc (set (tuple2 Int
  Int))) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 Int Int))) (v_OBF__xxee Int)
  (v_OBF__xxdd (set (tuple2 Int Int))) (v_OBF__xxcc (set (tuple2 Int Int)))
  (v_OBF__xxbb (set Int)) (v_OBF__xx Int) (v_OBF__wwff (set (tuple2 Int
  Int))) (v_OBF__wwee Int) (v_OBF__wwdd (set Int))
  (v_OBF__wwcc (set (tuple2 Int Int))) (v_OBF__wwbb (set Int))
  (v_OBF__ww (set Int)) (v_OBF__vvff (set (tuple2 Int Int)))
  (v_OBF__vvee Bool) (v_OBF__vvdd (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvcc (set (tuple2 Int Int))) (v_OBF__vvbb (set (tuple2 Int Int)))
  (v_OBF__vv Int) (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Int)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc (set Int))
  (v_OBF__uubb (set Int)) (v_OBF__uu (set Int)) (v_OBF__ttff (set (tuple2 Int
  Int))) (v_OBF__ttee Int) (v_OBF__ttdd (set (tuple2 Int Int)))
  (v_OBF__ttcc (set Int)) (v_OBF__ttbb (set Int)) (v_OBF__tt Int)
  (v_OBF__ssff (set Int)) (v_OBF__ssee Int) (v_OBF__ssdd (set (tuple2 Int
  Int))) (v_OBF__sscc (set Int)) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int)
  (v_OBF__rrdd (set (tuple2 Int Int))) (v_OBF__rrcc (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set Int))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Bool)))
  (v_OBF__ppee (set Int)) (v_OBF__ppdd (set (tuple2 Int Int)))
  (v_OBF__ppcc Int) (v_OBF__ppbb Int) (v_OBF__ooff Int)
  (v_OBF__ooee (set (tuple2 Int Int))) (v_OBF__oodd (set (tuple2 Int Int)))
  (v_OBF__oocc (set (tuple2 Int Int))) (v_OBF__oobb Int)
  (v_OBF__nnff (set Int)) (v_OBF__nnee (set (tuple2 Int Int)))
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Int)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Bool)))
  (v_OBF__mmee Bool) (v_OBF__mmdd (set Int)) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb (set Int)) (v_OBF__llff (set enum_OBF__ii))
  (v_OBF__llee Int) (v_OBF__lldd (set Int)) (v_OBF__llcc (set (tuple2 Int
  Int))) (v_OBF__llbb Int) (v_OBF__kkgg (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__kkff (set Int)) (v_OBF__kkee Int)
  (v_OBF__kkdd (set Int)) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb Int) (v_OBF__jjgg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__jjff (set Int)) (v_OBF__jjee Int)
  (v_OBF__jjdd (set enum_OBF__ii)) (v_OBF__jjcc (set (tuple2 Int Bool)))
  (v_OBF__jjbb (set Int)) (v_OBF__iigg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__iiff (set Int))
  (v_OBF__iiee (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iidd (set Int)) (v_OBF__iicc (set Int)) (v_OBF__iibb (set Int))
  (v_OBF__hhgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhff (set Int)) (v_OBF__hhee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__gggg (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__ggff (set Int)) (v_OBF__ggee enum_OBF__aa)
  (v_OBF__ggdd (set (tuple2 Int Int))) (v_OBF__ggcc (set (tuple2 Int Int)))
  (v_OBF__ggbb Int) (v_OBF__ffgg (set (tuple2 Int Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Int)
  (v_OBF__ffdd (set (tuple2 Int Int))) (v_OBF__ffcc (set Int))
  (v_OBF__ffbb Int) (v_OBF__eegg (set (tuple2 Int Int)))
  (v_OBF__eeff (set (tuple2 Int Int))) (v_OBF__eeee (set (tuple2 Int Int)))
  (v_OBF__eedd (set (tuple2 Int Int))) (v_OBF__eecc (set (tuple2 Int Int)))
  (v_OBF__eebb Int) (v_OBF__ddgg (set (tuple2 Int Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set (tuple2 Int
  Int))) (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__ccff (set Int))
  (v_OBF__ccee (set (tuple2 Int Int))) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int) (v_OBF__bbgg (set (tuple2 Int
  Int))) (v_OBF__bbff Bool) (v_OBF__bbee (set (tuple2 Int Int)))
  (v_OBF__bbdd Int) (v_OBF__bbcc (set Int)) (v_OBF__bbbb (set Int))
  (v_OBF__aagg (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd Int)
  (v_OBF__aacc (set (tuple2 Int Int))) (v_OBF__aabb Int))
  (=>
  (and (f1 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and (f2 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
  v_OBF__zz v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb
  v_OBF__yy v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb
  v_OBF__xx v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb
  v_OBF__ww v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb
  v_OBF__tt v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb
  v_OBF__rrff v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff
  v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg
  v_OBF__kkff v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg
  v_OBF__jjff v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg
  v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg
  v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb) (f13
  v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyff v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy
  v_OBF__xxff v_OBF__xxee v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx
  v_OBF__wwff v_OBF__wwee v_OBF__wwdd v_OBF__wwcc v_OBF__wwbb v_OBF__ww
  v_OBF__vvff v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb v_OBF__vv
  v_OBF__uuff v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb v_OBF__uu
  v_OBF__ttff v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssff v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rrff
  v_OBF__rree v_OBF__rrdd v_OBF__rrcc v_OBF__rrbb v_OBF__qqff v_OBF__qqee
  v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppff v_OBF__ppee v_OBF__ppdd
  v_OBF__ppcc v_OBF__ppbb v_OBF__ooff v_OBF__ooee v_OBF__oodd v_OBF__oocc
  v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc v_OBF__nnbb
  v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb v_OBF__llff
  v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkgg v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjgg v_OBF__jjff
  v_OBF__jjee v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iigg v_OBF__iiff
  v_OBF__iiee v_OBF__iidd v_OBF__iicc v_OBF__iibb v_OBF__hhgg v_OBF__hhff
  v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb v_OBF__gggg v_OBF__ggff
  v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg v_OBF__ffff
  v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg v_OBF__ddff
  v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg v_OBF__ccff
  v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg v_OBF__bbff
  v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg v_OBF__aaff
  v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb))) (mem1 v_OBF__aadd
  v_OBF__bbcc)))))
(check-sat)
