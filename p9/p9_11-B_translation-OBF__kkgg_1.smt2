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

(declare-fun t2tb2 ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb2 x))))

(declare-fun tb2t2 (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int))) (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb2 (tb2t2 j)) j) :pattern ((t2tb2 (tb2t2 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (infix_eqeq int (t2tb2 s1) (t2tb2 s2))
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
  (= (subset int (t2tb2 s1) (t2tb2 s2))
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
  (= (is_empty int (t2tb2 s)) (forall ((x Int)) (not (mem1 x s))))))

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem1 x (tb2t2 (empty int))))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun t2tb3 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb3 x))))

(declare-fun tb2t3 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb3 (tb2t3 j)) j) :pattern ((t2tb3 (tb2t3 j))) )))

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int)))
  (= (mem1 x (tb2t2 (add int (t2tb3 y) (t2tb2 s)))) (or (= x y) (mem1 x s))))))

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
  (= (mem1 x (tb2t2 (remove int (t2tb3 y) (t2tb2 s))))
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
  (= (tb2t2 (add int (t2tb3 x) (remove int (t2tb3 x) (t2tb2 s)))) s))))

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
  (= (mem1 x (tb2t2 (union int (t2tb2 s1) (t2tb2 s2))))
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
  (= (mem1 x (tb2t2 (inter int (t2tb2 s1) (t2tb2 s2))))
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
  (= (mem1 x (tb2t2 (diff int (t2tb2 s1) (t2tb2 s2))))
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
  (=> (not (is_empty int (t2tb2 s))) (mem1 (tb2t3 (choose int (t2tb2 s))) s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert (forall ((x Int)) (mem1 x (tb2t2 (all int)))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

(declare-fun t2tb (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb x))))

(declare-fun tb2t (uni) Bool)

;; BridgeL
  (assert (forall ((i Bool)) (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb (tb2t j)) j)) :pattern ((t2tb (tb2t j))) )))

(declare-fun t2tb1 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb1 x))))

(declare-fun tb2t1 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool))) (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb1 (tb2t1 j)) j)) :pattern ((t2tb1
                                                                 (tb2t1 j))) )))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb x) (t2tb1 b_bool))))

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
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t2 (empty int))))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t2 (add int (t2tb3 b) (t2tb2 (mk a (- b 1)))))))))

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
  (=> (mem (set1 (tuple21 a int)) f (relation int a s (t2tb2 t)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f)
  (and (mem a x s) (mem1 y t))))) (mem (set1 (tuple21 a int)) f
  (relation int a s (t2tb2 t))))))))

(declare-fun t2tb13 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb13 x))))

(declare-fun tb2t13 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb13 (tb2t13 j)) j) :pattern ((t2tb13 (tb2t13 j))) )))

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

(declare-fun t2tb23 ((tuple2 Int Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Int))) (sort (tuple21 int int) (t2tb23 x))))

(declare-fun tb2t23 (uni) (tuple2 Int Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Int)))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb23 (tb2t23 j)) j) :pattern ((t2tb23 (tb2t23 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb16 f)
  (relation int int (t2tb2 s) (t2tb2 t)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb16 f))
  (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (relation b int (t2tb2 s) t))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f)
  (and (mem1 x s) (mem b y t))))) (mem (set1 (tuple21 int b)) f
  (relation b int (t2tb2 s) t)))))))

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
  (forall ((r uni) (dom1 uni) (y Int))
  (! (and
     (=> (mem1 y (tb2t2 (image int a r dom1)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom1) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom1) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)))
     (mem1 y (tb2t2 (image int a r dom1))))) :pattern ((mem1
  y (tb2t2 (image int a r dom1)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom1 (set Int)) (y Int))
  (! (= (mem1 y (tb2t2 (image int int (t2tb16 r) (t2tb2 dom1))))
     (exists ((x Int))
     (and (mem1 x dom1) (mem (tuple21 int int)
     (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb16 r))))) :pattern ((mem1
  y (tb2t2 (image int int (t2tb16 r) (t2tb2 dom1))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Int)) (y uni))
  (! (= (mem b y (image b int r (t2tb2 dom1)))
     (exists ((x Int))
     (and (mem1 x dom1) (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r)))) :pattern ((mem
  b y (image b int r (t2tb2 dom1)))) ))))

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
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t)))
  (and
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f)
  (and (mem a x s) (mem1 y t))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb3 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb3 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb16 f)
  (infix_plmngt int int (t2tb2 s) (t2tb2 t)))
  (and
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb16 f))
  (and (mem1 x s) (mem1 y t))))
  (forall ((x Int) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y1))
  (t2tb16 f)) (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y2))
  (t2tb16 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
  (and
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f)
  (and (mem1 x s) (mem b y t))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb3 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb3 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t)))))))

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
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f) (mem1 x s))))))

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
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t)))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f) (mem1 y t))))))

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
  (=> (subset int (t2tb2 u) (t2tb2 t))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t)))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 u)))))))))

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
  (=> (mem1 x (tb2t2 (dom b int r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r))))
  (=> (exists ((y uni)) (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r))
  (mem1 x (tb2t2 (dom b int r)))))))))

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
  (=> (mem1 y (tb2t2 (ran int a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r))))
  (=> (exists ((x uni)) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r))
  (mem1 y (tb2t2 (ran int a r)))))))))

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
  (add (tuple21 a int) (Tuple2 a int x (t2tb3 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb2 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
  (empty (tuple21 int int))) (infix_plmngt int int (t2tb2 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (x Int) (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb3 x) y) (empty (tuple21 int b)))
  (infix_plmngt b int (t2tb2 s) t))))))

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
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t)) (mem1
  a (tb2t2 (dom b int f)))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb3 a) (apply b int f (t2tb3 a))) f)))))

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
  (and (mem (set1 (tuple21 int b)) f (infix_mnmngt b int (t2tb2 s) t)) (mem1
  a s)) (mem (tuple21 int b)
  (Tuple2 int b (t2tb3 a) (apply b int f (t2tb3 a))) f)))))

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
     (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t)))
     (mem a x (dom int a f))) (mem1 (tb2t3 (apply int a f x)) t)) :pattern ((mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t)))
  (tb2t3 (apply int a f x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 int int)) (t2tb16 f)
     (infix_plmngt int int (t2tb2 s) (t2tb2 t))) (mem1 x
     (tb2t2 (dom int int (t2tb16 f))))) (mem1
     (tb2t3 (apply int int (t2tb16 f) (t2tb3 x))) t)) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb16 f)
  (infix_plmngt int int (t2tb2 s) (t2tb2 t)))
  (tb2t3 (apply int int (t2tb16 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x Int) (f uni) (s (set Int)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
     (mem1 x (tb2t2 (dom b int f)))) (mem b (apply b int f (t2tb3 x)) t)) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
  (apply b int f (t2tb3 x))) ))))

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
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb2 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb2 t) u))
  (and (mem a x (dom int a f)) (mem1 (tb2t3 (apply int a f x))
  (tb2t2 (dom c int g))))))
  (= (apply c a (semicolon c int a f g) x) (apply c int g (apply int a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int Int))) (g uni) (s (set Int))
  (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int int)) (t2tb16 f)
  (infix_plmngt int int (t2tb2 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb2 t) u))
  (and (mem1 x (tb2t2 (dom int int (t2tb16 f)))) (mem1
  (tb2t3 (apply int int (t2tb16 f) (t2tb3 x))) (tb2t2 (dom c int g))))))
  (= (apply c int (semicolon c int int (t2tb16 f) g) (t2tb3 x)) (apply c 
                                                                int g
                                                                (apply 
                                                                int int
                                                                (t2tb16 f)
                                                                (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x Int) (f uni) (g uni) (s (set Int)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t2 (dom b int f))) (mem b (apply b int f (t2tb3 x))
  (dom c b g)))))
  (= (apply c int (semicolon c b int f g) (t2tb3 x)) (apply c b g
                                                     (apply b int f
                                                     (t2tb3 x))))))))

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
  (=> (mem (set1 (tuple21 int b)) f (infix_gtmngt b int (t2tb2 s) t))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=> (= (apply b int f (t2tb3 x)) (apply b int f (t2tb3 y))) (= x y)))))))))

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
  (= (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
  (id int (t2tb2 s))) (and (mem1 x s) (= x y)))))

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
  (= (seq_length a n s) (infix_mnmngt a int (t2tb2 (mk 1 n)) s)))))

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
  (infix_mnmngt a int (t2tb2 (mk 1 (size a r))) s))))))

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
  (=> (is_finite_subset int (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset int (add int (t2tb3 x) (t2tb2 s1))
  (t2tb2 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset int (add int (t2tb3 x) (t2tb2 s1))
  (t2tb2 s2) (+ c 1)))))))

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
  (=> (is_finite_subset int (t2tb2 z) (t2tb2 z1) z2)
  (or
  (or
  (exists ((s (set Int)))
  (and (and (= z (tb2t2 (empty int))) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb2 s1) (t2tb2 s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1)
  (and (and (= z (tb2t2 (add int (t2tb3 x) (t2tb2 s1)))) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb2 s1) (t2tb2 s2) c)
  (and (mem1 x s2)
  (and (not (mem1 x s1))
  (and (and (= z (tb2t2 (add int (t2tb3 x) (t2tb2 s1)))) (= z1 s2))
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
  (=> (<= a b) (is_finite_subset int (t2tb2 (mk a b)) (t2tb2 integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb2 (mk a b)) (t2tb2 integer) 0))))

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

(declare-fun t2tb11 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb11 x))))

(declare-fun tb2t11 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb11 (tb2t11 j)) j) :pattern ((t2tb11 (tb2t11 j))) )))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb2 s1) (finite_subsets int (t2tb2 s2)))
  (=> (mem1 x s2) (mem (set1 int) (add int (t2tb3 x) (t2tb2 s1))
  (finite_subsets int (t2tb2 s2)))))))

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
  (! (=> (mem (set1 int) (t2tb2 s1) (finite_subsets int (t2tb2 s2)))
     (=> (not (mem1 x s1))
     (= (card int (add int (t2tb3 x) (t2tb2 s1))) (+ (card int (t2tb2 s1)) 1)))) :pattern ((mem
  (set1 int) (t2tb2 s1) (finite_subsets int (t2tb2 s2)))
  (card int (add int (t2tb3 x) (t2tb2 s1)))) )))

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
  (! (=> (mem (set1 int) (t2tb2 s1) (finite_subsets int (t2tb2 s2)))
     (=> (mem1 x s1)
     (= (card int (add int (t2tb3 x) (t2tb2 s1))) (card int (t2tb2 s1))))) :pattern ((mem
  (set1 int) (t2tb2 s1) (finite_subsets int (t2tb2 s2)))
  (card int (add int (t2tb3 x) (t2tb2 s1)))) )))

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
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y))
     (times int a a1 (t2tb2 b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb3 y)) (times int a a1 (t2tb2 b)))) ))))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set Int)) (x Int) (y Int))
  (! (= (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
     (times int int (t2tb2 a) (t2tb2 b))) (and (mem1 x a) (mem1 y b))) :pattern ((mem
  (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
  (times int int (t2tb2 a) (t2tb2 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set Int)) (b1 uni) (x Int) (y uni))
  (! (= (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y)
     (times b int (t2tb2 a) b1)) (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 int b) (Tuple2 int b (t2tb3 x) y) (times b int (t2tb2 a) b1))) ))))

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
  (=> (subset (tuple21 a int) r (times int a u (t2tb2 v)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)
  (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)
  (and (mem a x u) (mem1 y v))))) (subset (tuple21 a int) r
  (times int a u (t2tb2 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int Int))) (u (set Int)) (v (set Int)))
  (= (subset (tuple21 int int) (t2tb16 r)
  (times int int (t2tb2 u) (t2tb2 v)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb16 r))
  (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set Int)) (v uni))
  (and
  (=> (subset (tuple21 int b) r (times b int (t2tb2 u) v))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r)
  (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r)
  (and (mem1 x u) (mem b y v))))) (subset (tuple21 int b) r
  (times b int (t2tb2 u) v)))))))

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
     (= (apply b int (times b int (t2tb2 s) (add b y (empty b))) (t2tb3 x)) y))) :pattern (
  (apply b int (times b int (t2tb2 s) (add b y (empty b))) (t2tb3 x))) ))))

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
  (=> (subset int (t2tb2 f) (ran int e1 r))
  (= (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y))
  (range_restriction int e1 r (t2tb2 f)))
  (and (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y)) r) (mem1 y f)))))))

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
  (= (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y))
  (range_substraction int e1 r (t2tb2 f)))
  (and (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y)) r) (not (mem1 y f)))))))

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
  (= (mem (tuple21 int e2) (Tuple2 int e2 (t2tb3 x) y)
  (domain_restriction e2 int (t2tb2 f) r))
  (and (mem (tuple21 int e2) (Tuple2 int e2 (t2tb3 x) y) r) (mem1 x f))))))

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
  (=> (subset int (t2tb2 f) (dom e2 int r))
  (= (mem (tuple21 int e2) (Tuple2 int e2 (t2tb3 x) y)
  (domain_substraction e2 int (t2tb2 f) r))
  (and (mem (tuple21 int e2) (Tuple2 int e2 (t2tb3 x) y) r) (not (mem1 x f))))))))

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
  (= (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) (infix_lspl b int q r))
  (ite (mem1 x (tb2t2 (dom b int r))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb3 x) y) r) (mem (tuple21 int b)
  (Tuple2 int b (t2tb3 x) y) q))))))

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
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb2 s) t)))
     (=> (mem1 x (tb2t2 (dom b int g)))
     (= (apply b int (infix_lspl b int f g) (t2tb3 x)) (apply b int g
                                                       (t2tb3 x))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t)) (mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb2 s) t))
  (apply b int (infix_lspl b int f g) (t2tb3 x))) ))))

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
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb2 s) t)))
     (=> (not (mem1 x (tb2t2 (dom b int g))))
     (=> (mem1 x (tb2t2 (dom b int f)))
     (= (apply b int (infix_lspl b int f g) (t2tb3 x)) (apply b int f
                                                       (t2tb3 x)))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb2 s) t))
  (apply b int (infix_lspl b int f g) (t2tb3 x))) :pattern ((mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb2 s) t))
  (apply b int (infix_lspl b int f g) (t2tb3 x))) ))))

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

(declare-fun t2tb4 ((set enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__aa))) (sort (set1 enum_OBF__aa1) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__aa)))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__aa1) j) (= (t2tb4 (tb2t4 j)) j)) :pattern (
  (t2tb4 (tb2t4 j))) )))

(declare-fun t2tb5 (enum_OBF__aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__aa)) (sort enum_OBF__aa1 (t2tb5 x))))

(declare-fun tb2t5 (uni) enum_OBF__aa)

;; BridgeL
  (assert
  (forall ((i enum_OBF__aa))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__aa1 j) (= (t2tb5 (tb2t5 j)) j)) :pattern ((t2tb5
                                                                   (tb2t5 j))) )))

;; set_enum_OBF__aa_axiom
  (assert
  (forall ((x enum_OBF__aa)) (mem enum_OBF__aa1 (t2tb5 x)
  (t2tb4 set_enum_OBF__aa))))

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

(declare-fun t2tb6 ((set enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__ii))) (sort (set1 enum_OBF__ii1) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__ii)))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__ii1) j) (= (t2tb6 (tb2t6 j)) j)) :pattern (
  (t2tb6 (tb2t6 j))) )))

(declare-fun t2tb7 (enum_OBF__ii) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__ii)) (sort enum_OBF__ii1 (t2tb7 x))))

(declare-fun tb2t7 (uni) enum_OBF__ii)

;; BridgeL
  (assert
  (forall ((i enum_OBF__ii))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__ii1 j) (= (t2tb7 (tb2t7 j)) j)) :pattern ((t2tb7
                                                                   (tb2t7 j))) )))

;; set_enum_OBF__ii_axiom
  (assert
  (forall ((x enum_OBF__ii)) (mem enum_OBF__ii1 (t2tb7 x)
  (t2tb6 set_enum_OBF__ii))))

(declare-fun f1 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

(declare-fun t2tb8 ((set (set (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) int))) (t2tb8 x))))

(declare-fun tb2t8 (uni) (set (set (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb8 (tb2t8 j)) j) :pattern ((t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb9 x))))

(declare-fun tb2t9 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb9 (tb2t9 j)) j) :pattern ((t2tb9 (tb2t9 j))) )))

(declare-fun t2tb10 ((set (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb10 (tb2t10 j)) j) :pattern ((t2tb10 (tb2t10 j))) )))

(declare-fun t2tb12 ((set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

(declare-fun t2tb14 ((set (tuple2 Int Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Bool)))) (sort (set1 (tuple21 int bool))
  (t2tb14 x))))

(declare-fun tb2t14 (uni) (set (tuple2 Int Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Bool))))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

(declare-fun t2tb15 ((set (tuple2 Bool Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Int)))) (sort (set1 (tuple21 bool int))
  (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (tuple2 Bool Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Int))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

(declare-fun t2tb17 ((set (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))) (sort
  (set1 (tuple21 (tuple21 int int) int)) (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

(declare-fun t2tb18 ((set (set (tuple2 Int Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Bool))))) (sort
  (set1 (set1 (tuple21 int bool))) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (set (tuple2 Int Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Bool)))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb18 (tb2t18 j)) j) :pattern ((t2tb18 (tb2t18 j))) )))

(declare-fun t2tb19 ((set (tuple2 Int (tuple2 Int (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int (tuple2 Int Int)))))) (sort
  (set1 (tuple21 int (tuple21 int (tuple21 int int)))) (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (tuple2 Int (tuple2 Int (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int (tuple2 Int Int))))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

(declare-fun t2tb20 ((set (tuple2 Int (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int Int))))) (sort
  (set1 (tuple21 int (tuple21 int int))) (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (tuple2 Int (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int Int)))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

(declare-fun t2tb21 ((set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb21 (tb2t21 j)) j) :pattern ((t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((set (tuple2 Int enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int enum_OBF__aa)))) (sort
  (set1 (tuple21 int enum_OBF__aa1)) (t2tb22 x))))

(declare-fun tb2t22 (uni) (set (tuple2 Int enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int enum_OBF__aa))))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb22 (tb2t22 j)) j) :pattern ((t2tb22 (tb2t22 j))) )))

;; f1_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb2 v_OBF__kkcc) (power int (t2tb2 v_OBF__cccc)))
  (mem (set1 int) (t2tb2 v_OBF__jjcc) (power int (t2tb2 v_OBF__cccc)))) (mem
  (set1 int) (t2tb2 v_OBF__hhcc) (power int (t2tb2 v_OBF__cccc)))) (mem
  (set1 int) (t2tb2 v_OBF__ffcc) (power int (t2tb2 v_OBF__cccc)))) (mem
  (set1 int) (t2tb2 v_OBF__eecc) (power int (t2tb2 v_OBF__cccc)))) (mem
  (set1 int) (t2tb2 v_OBF__ddcc) (power int (t2tb2 v_OBF__cccc)))) (mem
  (set1 int) (t2tb2 v_OBF__zzbb) (power int (t2tb2 v_OBF__cccc)))) (mem1
  v_OBF__xxbb v_OBF__cccc)) (infix_eqeq int (t2tb2 v_OBF__mmbb)
  (union int
  (union int
  (union int
  (union int
  (union int
  (union int (union int (t2tb2 v_OBF__kkcc) (t2tb2 v_OBF__jjcc))
  (t2tb2 v_OBF__hhcc)) (t2tb2 v_OBF__ffcc)) (t2tb2 v_OBF__eecc))
  (t2tb2 v_OBF__ddcc)) (t2tb2 v_OBF__zzbb))
  (add int (t2tb3 v_OBF__xxbb) (empty int))))) (mem (set1 int)
  (t2tb2 v_OBF__jjcc)
  (power int (diff int (t2tb2 v_OBF__mmbb) (t2tb2 v_OBF__kkcc))))) (mem
  (set1 int) (t2tb2 v_OBF__hhcc)
  (power int
  (diff int (t2tb2 v_OBF__mmbb)
  (union int (t2tb2 v_OBF__kkcc) (t2tb2 v_OBF__jjcc)))))) (mem (set1 int)
  (t2tb2 v_OBF__ffcc)
  (power int
  (diff int (t2tb2 v_OBF__mmbb)
  (union int (union int (t2tb2 v_OBF__kkcc) (t2tb2 v_OBF__jjcc))
  (t2tb2 v_OBF__hhcc)))))) (mem (set1 int) (t2tb2 v_OBF__eecc)
  (power int
  (diff int (t2tb2 v_OBF__mmbb)
  (union int
  (union int (union int (t2tb2 v_OBF__kkcc) (t2tb2 v_OBF__jjcc))
  (t2tb2 v_OBF__hhcc)) (t2tb2 v_OBF__ffcc)))))) (mem (set1 int)
  (t2tb2 v_OBF__ddcc)
  (power int
  (diff int (t2tb2 v_OBF__mmbb)
  (union int
  (union int
  (union int (union int (t2tb2 v_OBF__kkcc) (t2tb2 v_OBF__jjcc))
  (t2tb2 v_OBF__hhcc)) (t2tb2 v_OBF__ffcc)) (t2tb2 v_OBF__eecc)))))) (mem
  (set1 int) (t2tb2 v_OBF__zzbb)
  (power int
  (diff int (t2tb2 v_OBF__mmbb)
  (union int
  (union int
  (union int
  (union int (union int (t2tb2 v_OBF__kkcc) (t2tb2 v_OBF__jjcc))
  (t2tb2 v_OBF__hhcc)) (t2tb2 v_OBF__ffcc)) (t2tb2 v_OBF__eecc))
  (t2tb2 v_OBF__ddcc)))))) (mem1 v_OBF__xxbb v_OBF__mmbb))
  (not (mem1 v_OBF__xxbb v_OBF__kkcc))) (not (mem1 v_OBF__xxbb v_OBF__jjcc)))
  (not (mem1 v_OBF__xxbb v_OBF__hhcc))) (not (mem1 v_OBF__xxbb v_OBF__ffcc)))
  (not (mem1 v_OBF__xxbb v_OBF__eecc))) (not (mem1 v_OBF__xxbb v_OBF__ddcc)))
  (not (mem1 v_OBF__xxbb v_OBF__zzbb))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__rrcc)
  (relation int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__wwcc)
  (relation int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__iiff)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__jjff)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int bool)) (t2tb14 v_OBF__kkff)
  (relation bool int (t2tb2 v_OBF__bbcc) (t2tb1 b_bool)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__wwcc)
  (power (tuple21 int int) (t2tb16 v_OBF__rrcc)))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__llff)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb16 v_OBF__iiff) (t2tb16 v_OBF__rrcc))
  (semicolon int int int (t2tb16 v_OBF__jjff)
  (inverse int int (t2tb16 v_OBF__rrcc)))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__mmff)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb16 v_OBF__iiff) (t2tb16 v_OBF__wwcc))
  (semicolon int int int (t2tb16 v_OBF__jjff)
  (inverse int int (t2tb16 v_OBF__rrcc)))))) (infix_eqeq int
  (t2tb2 v_OBF__nnff)
  (image int bool (inverse bool int (t2tb14 v_OBF__kkff))
  (add bool (t2tb true) (empty bool))))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__iiff)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__iiff)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__jjff)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__jjff)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 (tuple21 int bool)) (t2tb14 v_OBF__kkff)
  (infix_plmngt bool int (t2tb2 v_OBF__bbcc) (t2tb1 b_bool)))) (infix_eqeq
  int (dom bool int (t2tb14 v_OBF__kkff)) (t2tb2 v_OBF__bbcc))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__llff)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__mmff)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ooff)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ppff)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__dddd)))) (mem
  (set1 int) (t2tb2 v_OBF__nnff) (power int (t2tb2 v_OBF__bbcc))))
  (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__qqff)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__nnff)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__ppff)
  (direct_product int int int (t2tb16 v_OBF__llff) (t2tb16 v_OBF__ooff)))))
  (add int (t2tb3 v_OBF__ggbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__rrff)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__nnff)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__ppff)
  (direct_product int int int (t2tb16 v_OBF__llff) (t2tb16 v_OBF__ooff)))))
  (add int (t2tb3 v_OBF__hhbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__hhee)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__nnff)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__ppff)
  (direct_product int int int (t2tb16 v_OBF__llff) (t2tb16 v_OBF__ooff)))))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__ggee)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__nnff)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__ppff)
  (direct_product int int int (t2tb16 v_OBF__mmff) (t2tb16 v_OBF__ooff)))))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__mmff) (power (tuple21 int int) (t2tb16 v_OBF__llff)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ooff)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__ooff)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 int) (ran int int (t2tb16 v_OBF__ppff))
  (power int
  (union int
  (union int (add int (t2tb3 v_OBF__ggbb) (empty int))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (add int (t2tb3 v_OBF__ffbb) (empty int)))))) (mem (set1 int)
  (t2tb2 v_OBF__bbcc) (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_OBF__bbcc) (empty int)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__hhee)
  (relation int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ggee)
  (relation int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb2 v_OBF__iiee) (power int (t2tb2 v_OBF__bbbb))))
  (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__ssff)
  (times int int
  (diff int (dom int int (t2tb16 v_OBF__hhee))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb16 v_OBF__hhee) (t2tb16 v_OBF__hhee))
  (id int (t2tb2 v_OBF__bbbb))))) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ggee)
  (power (tuple21 int int) (t2tb16 v_OBF__hhee)))) (mem1 v_OBF__uucc
  v_OBF__bbbb)) (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__qqff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__rrff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb)))))
  (not (= v_OBF__uucc v_OBF__ssbb))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__ttff)
  (union (tuple21 int int) (t2tb16 v_OBF__qqff)
  (semicolon int int int (t2tb16 v_OBF__qqff)
  (times int int (add int (t2tb3 v_OBF__uucc) (empty int))
  (t2tb2 v_OBF__bbbb)))))) (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__uuff)
  (union (tuple21 int int) (t2tb16 v_OBF__rrff)
  (semicolon int int int (t2tb16 v_OBF__rrff)
  (times int int (add int (t2tb3 v_OBF__uucc) (empty int))
  (t2tb2 v_OBF__bbbb)))))) (mem1 v_OBF__llbb v_OBF__ppdd)) (mem1 v_OBF__ssbb
  v_OBF__bbbb)) (mem (set1 int) (t2tb2 v_OBF__uu)
  (power int (t2tb2 v_OBF__cccc)))) (mem (set1 int) (t2tb2 v_OBF__iibb)
  (power int (t2tb2 v_OBF__cccc)))) (mem (set1 int) (t2tb2 v_OBF__mmbb)
  (power int (t2tb2 v_OBF__cccc)))) (mem (set1 int) (t2tb2 v_OBF__nnbb)
  (power int (t2tb2 v_OBF__cccc)))) (mem1 v_OBF__oobb v_OBF__cccc)) (mem1
  v_OBF__ppbb v_OBF__cccc)) (mem1 v_OBF__qqbb v_OBF__cccc)) (mem1 v_OBF__rrbb
  v_OBF__cccc)) (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__ttff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__uuff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ssff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem (set1 int)
  (t2tb2 v_OBF__vvff) (power int (t2tb2 v_OBF__bbbb)))) (mem (set1 int)
  (t2tb2 v_OBF__iibb) (power int (t2tb2 v_OBF__uu)))) (mem (set1 int)
  (t2tb2 v_OBF__mmbb)
  (power int (diff int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__uu))))) (mem
  (set1 int) (t2tb2 v_OBF__nnbb)
  (power int
  (diff int (t2tb2 v_OBF__cccc)
  (union int (t2tb2 v_OBF__uu) (t2tb2 v_OBF__mmbb))))))
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
  (infix_eqeq int (t2tb2 v_OBF__cccc)
  (union int
  (union int (union int (t2tb2 v_OBF__uu) (t2tb2 v_OBF__mmbb))
  (t2tb2 v_OBF__nnbb))
  (union int
  (union int
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int)))
  (add int (t2tb3 v_OBF__qqbb) (empty int)))
  (add int (t2tb3 v_OBF__rrbb) (empty int)))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__wwff)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb2 v_OBF__uu) (t2tb16 v_OBF__ttff))
  (times int int (t2tb2 v_OBF__nnbb) (t2tb2 v_OBF__vvff)))
  (times int int
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int))) (t2tb2 v_OBF__vvff)))
  (times int int (t2tb2 v_OBF__mmbb)
  (add int (t2tb3 v_OBF__ssbb) (empty int))))
  (times int int (t2tb2 v_OBF__iibb) (t2tb2 v_OBF__bbbb)))
  (times int int (add int (t2tb3 v_OBF__qqbb) (empty int))
  (t2tb2 v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__rrbb) (t2tb3 v_OBF__ssbb))
  (empty (tuple21 int int)))))) (infix_eqeq (tuple21 (tuple21 int int) int)
  (t2tb17 v_OBF__xxff)
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb2 v_OBF__uu) (t2tb16 v_OBF__uuff))
  (times int int (t2tb2 v_OBF__nnbb) (t2tb2 v_OBF__vvff)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__rrbb) (t2tb3 v_OBF__ssbb))
  (empty (tuple21 int int)))) (t2tb2 v_OBF__ppdd))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int))) (t2tb2 v_OBF__vvff))
  (add int (t2tb3 v_OBF__llbb) (empty int)))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__yyff)
  (domain_restriction int int (t2tb2 v_OBF__uu) (t2tb16 v_OBF__ssff)))) (mem1
  v_OBF__wwdd integer)) (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__zzff)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__aagg)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))
  (<= 1 v_OBF__wwdd)) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb10 v_OBF__bbgg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb2 integer) (t2tb4 set_enum_OBF__aa))
  (t2tb2 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb10 v_OBF__ccgg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb2 integer) (t2tb4 set_enum_OBF__aa))
  (t2tb2 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb10 v_OBF__ddgg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb2 integer) (t2tb4 set_enum_OBF__aa))
  (t2tb2 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb10 v_OBF__eegg)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb2 integer) (t2tb4 set_enum_OBF__aa))
  (t2tb2 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb10 v_OBF__aaee)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb2 integer) (t2tb4 set_enum_OBF__aa))
  (t2tb2 integer))))) (infix_eqeq (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb10 v_OBF__bbgg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 0) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb5 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb5 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__cc) (empty enum_OBF__aa1))))
  (add int (t2tb3 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 v_OBF__ccgg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 0) (empty int))
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb5 E_OBF__hh) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb5 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb3 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 v_OBF__ddgg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 1) (empty int))
  (add enum_OBF__aa1 (t2tb5 E_OBF__cc) (empty enum_OBF__aa1)))
  (add int (t2tb3 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 v_OBF__eegg)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 1) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb5 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb5 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__hh) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb5 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb3 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 v_OBF__aaee)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 v_OBF__bbgg)
  (t2tb10 v_OBF__ccgg)) (t2tb10 v_OBF__ddgg)) (t2tb10 v_OBF__eegg)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__wwff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb17 v_OBF__xxff)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (t2tb2 v_OBF__ppdd))))) (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__yyff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__zzff)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__aagg)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb12 v_OBF__ffgg)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__wwff) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ggbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb17 v_OBF__xxff)
  (add int (t2tb3 v_OBF__hhbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__yyff) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__zzff) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ccee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__aagg) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ddee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (t2tb2 v_OBF__ppdd)) (add int (t2tb3 v_OBF__eeee) (empty int)))))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb12 v_OBF__ffgg)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (t2tb2 v_OBF__ppdd)) (t2tb2 v_OBF__dddd))))) (mem1 v_OBF__ggbb
  v_OBF__dddd)) (mem1 v_OBF__hhbb v_OBF__dddd)) (mem1 v_OBF__ffbb
  v_OBF__dddd)) (mem1 v_OBF__ccee v_OBF__dddd)) (mem1 v_OBF__ddee
  v_OBF__dddd)) (mem1 v_OBF__eeee v_OBF__dddd))
  (not (= v_OBF__ggbb v_OBF__hhbb))) (not (= v_OBF__ggbb v_OBF__ffbb)))
  (not (= v_OBF__ggbb v_OBF__ccee))) (not (= v_OBF__ggbb v_OBF__ddee)))
  (not (= v_OBF__ggbb v_OBF__eeee))) (not (= v_OBF__hhbb v_OBF__ggbb)))
  (not (= v_OBF__hhbb v_OBF__ffbb))) (not (= v_OBF__hhbb v_OBF__ccee)))
  (not (= v_OBF__hhbb v_OBF__ddee))) (not (= v_OBF__hhbb v_OBF__eeee)))
  (not (= v_OBF__ffbb v_OBF__ggbb))) (not (= v_OBF__ffbb v_OBF__hhbb)))
  (not (= v_OBF__ffbb v_OBF__ccee))) (not (= v_OBF__ffbb v_OBF__ddee)))
  (not (= v_OBF__ffbb v_OBF__eeee))) (not (= v_OBF__ccee v_OBF__ggbb)))
  (not (= v_OBF__ccee v_OBF__hhbb))) (not (= v_OBF__ccee v_OBF__ffbb)))
  (not (= v_OBF__ccee v_OBF__ddee))) (not (= v_OBF__ccee v_OBF__eeee)))
  (not (= v_OBF__ddee v_OBF__ggbb))) (not (= v_OBF__ddee v_OBF__hhbb)))
  (not (= v_OBF__ddee v_OBF__ffbb))) (not (= v_OBF__ddee v_OBF__ccee)))
  (not (= v_OBF__ddee v_OBF__eeee))) (not (= v_OBF__eeee v_OBF__ggbb)))
  (not (= v_OBF__eeee v_OBF__hhbb))) (not (= v_OBF__eeee v_OBF__ffbb)))
  (not (= v_OBF__eeee v_OBF__ccee))) (not (= v_OBF__eeee v_OBF__ddee))) (mem
  (set1 int) (t2tb2 v_OBF__cccc) (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_OBF__cccc) (empty int)))) (mem (set1 int)
  (t2tb2 v_OBF__bbbb) (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_OBF__bbbb) (empty int)))) (mem (set1 int)
  (t2tb2 v_OBF__ppdd) (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_OBF__ppdd) (empty int)))) (mem (set1 int)
  (t2tb2 v_OBF__dddd) (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_OBF__dddd) (empty int)))))))

(declare-fun f2 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

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
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__qqcc)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__sscc)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int bool)) (t2tb14 v_OBF__ppcc)
  (relation bool int (t2tb2 v_OBF__bbcc) (t2tb1 b_bool)))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__aadd)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__rrcc))
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc)))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__bbdd)
  (inter (tuple21 int int)
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__wwcc))
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc)))))) (infix_eqeq int
  (t2tb2 v_OBF__ccdd)
  (image int bool (inverse bool int (t2tb14 v_OBF__ppcc))
  (add bool (t2tb true) (empty bool))))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__qqcc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__qqcc)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__sscc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__sscc)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 (tuple21 int bool)) (t2tb14 v_OBF__ppcc)
  (infix_plmngt bool int (t2tb2 v_OBF__bbcc) (t2tb1 b_bool)))) (infix_eqeq
  int (dom bool int (t2tb14 v_OBF__ppcc)) (t2tb2 v_OBF__bbcc))) (mem
  (set1 enum_OBF__ii1) (t2tb6 v_OBF__uubb)
  (power enum_OBF__ii1 (t2tb6 set_enum_OBF__ii)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__aadd)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__bbdd)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ttcc)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__iicc)
  (relation int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__dddd)))) (mem
  (set1 int) (t2tb2 v_OBF__ccdd) (power int (t2tb2 v_OBF__bbcc)))) (mem
  (set1 int) (t2tb2 v_OBF__jjbb) (power int (t2tb2 v_OBF__bbcc)))) (mem
  (set1 int) (t2tb2 v_OBF__eedd) (power int (t2tb2 v_OBF__bbcc)))) (mem
  (set1 int) (t2tb2 v_OBF__ww) (power int (t2tb2 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb2 v_OBF__zz) (power int (t2tb2 v_OBF__bbcc)))) (mem
  (set1 int) (t2tb2 v_OBF__ffdd) (power int (t2tb2 v_OBF__bbcc))))
  (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__ggdd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__ccdd)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__iicc)
  (direct_product int int int (t2tb16 v_OBF__aadd) (t2tb16 v_OBF__ttcc)))))
  (add int (t2tb3 v_OBF__ggbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__hhdd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__ccdd)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__iicc)
  (direct_product int int int (t2tb16 v_OBF__aadd) (t2tb16 v_OBF__ttcc)))))
  (add int (t2tb3 v_OBF__hhbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__iidd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__ccdd)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__iicc)
  (direct_product int int int (t2tb16 v_OBF__aadd) (t2tb16 v_OBF__ttcc)))))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__jjdd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb2 v_OBF__ccdd)
  (direct_product (tuple21 int int) int int (t2tb16 v_OBF__iicc)
  (direct_product int int int (t2tb16 v_OBF__bbdd) (t2tb16 v_OBF__ttcc)))))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__bbdd) (power (tuple21 int int) (t2tb16 v_OBF__aadd)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ttcc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__ttcc)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 int) (ran int int (t2tb16 v_OBF__iicc))
  (power int
  (union int
  (union int (add int (t2tb3 v_OBF__ggbb) (empty int))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb2 v_OBF__jjbb)
  (inter int (t2tb2 v_OBF__ccdd)
  (image int int (inverse int int (t2tb16 v_OBF__aadd))
  (add int (t2tb3 v_OBF__tt) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb2 v_OBF__eedd)
  (inter int
  (inter int (t2tb2 v_OBF__ccdd)
  (image int int (inverse int int (t2tb16 v_OBF__aadd))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb2 v_OBF__ww)
  (image int int (t2tb16 v_OBF__ttcc) (t2tb2 v_OBF__eedd)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb2 v_OBF__zz)
  (inter int
  (inter int (t2tb2 v_OBF__ccdd)
  (image int int (inverse int int (t2tb16 v_OBF__bbdd))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb2 v_OBF__ffdd)
  (inter int
  (inter int
  (inter int (t2tb2 v_OBF__ccdd)
  (image int int (inverse int int (t2tb16 v_OBF__aadd))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__ttcc))
  (union int (add int (t2tb3 v_OBF__vv) (empty int))
  (add int (t2tb3 v_OBF__uucc) (empty int)))))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__iidd)
  (relation int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__jjdd)
  (relation int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb2 v_OBF__yy) (power int (t2tb2 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__kkdd)
  (times int int
  (diff int
  (dom int int
  (union (tuple21 int int) (t2tb16 v_OBF__jjdd)
  (range_substraction int int (t2tb16 v_OBF__iidd)
  (image int int
  (times int int (add int (t2tb3 0) (empty int))
  (diff int (t2tb2 v_OBF__yy) (add int (t2tb3 v_OBF__vv) (empty int))))
  (add int (t2tb3 v_OBF__xx) (empty int))))))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb16 v_OBF__iidd) (t2tb16 v_OBF__iidd))
  (id int (t2tb2 v_OBF__bbbb))))) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__jjdd)
  (power (tuple21 int int) (t2tb16 v_OBF__iidd)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ggdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__hhdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__lldd)
  (union (tuple21 int int) (t2tb16 v_OBF__ggdd)
  (semicolon int int int (t2tb16 v_OBF__ggdd)
  (times int int (add int (t2tb3 v_OBF__uucc) (empty int))
  (t2tb2 v_OBF__bbbb)))))) (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__mmdd)
  (union (tuple21 int int) (t2tb16 v_OBF__hhdd)
  (semicolon int int int (t2tb16 v_OBF__hhdd)
  (times int int (add int (t2tb3 v_OBF__uucc) (empty int))
  (t2tb2 v_OBF__bbbb)))))) (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__lldd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__mmdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__kkdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem (set1 int)
  (t2tb2 v_OBF__ttbb) (power int (t2tb2 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__nndd)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb2 v_OBF__uu) (t2tb16 v_OBF__lldd))
  (times int int (t2tb2 v_OBF__nnbb) (t2tb2 v_OBF__ttbb)))
  (times int int
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int))) (t2tb2 v_OBF__ttbb)))
  (times int int (t2tb2 v_OBF__mmbb)
  (add int (t2tb3 v_OBF__ssbb) (empty int))))
  (dom int (tuple21 int int)
  (range_restriction int (tuple21 int int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__iibb) (t2tb2 v_OBF__bbbb))
  (add int (t2tb3 1) (empty int))) (add int (t2tb3 v_OBF__xx) (empty int)))))
  (times int int (add int (t2tb3 v_OBF__qqbb) (empty int))
  (t2tb2 v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__rrbb) (t2tb3 v_OBF__ssbb))
  (empty (tuple21 int int)))))) (infix_eqeq (tuple21 (tuple21 int int) int)
  (t2tb17 v_OBF__oodd)
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb2 v_OBF__uu) (t2tb16 v_OBF__mmdd))
  (times int int (t2tb2 v_OBF__nnbb) (t2tb2 v_OBF__ttbb)))
  (dom bool (tuple21 int int)
  (range_restriction bool (tuple21 int int)
  (times bool (tuple21 int int)
  (times int int (t2tb2 v_OBF__mmbb)
  (add int (t2tb3 v_OBF__ssbb) (empty int)))
  (add bool (t2tb false) (empty bool)))
  (add bool (t2tb v_OBF__yybb) (empty bool)))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__rrbb) (t2tb3 v_OBF__ssbb))
  (empty (tuple21 int int)))) (t2tb2 v_OBF__ppdd))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int))) (t2tb2 v_OBF__ttbb))
  (add int (t2tb3 v_OBF__llbb) (empty int)))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__qqdd)
  (domain_restriction int int (t2tb2 v_OBF__uu) (t2tb16 v_OBF__kkdd)))) (mem1
  v_OBF__rrdd v_OBF__bbbb)) (mem1 v_OBF__ssdd integer)) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ttdd)
  (relation int int (t2tb2 integer) (t2tb2 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__uudd)
  (relation int int (t2tb2 integer) (t2tb2 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__vvdd)
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb3 v_OBF__wwdd) (t2tb3 0))
  (empty (tuple21 int int))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__ssdd) (t2tb3 v_OBF__xx))
  (empty (tuple21 int int))))))) (infix_eqeq (tuple21 int int)
  (t2tb16 v_OBF__xxdd)
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb3 0) (t2tb3 0))
  (empty (tuple21 int int))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__ssdd) (t2tb3 v_OBF__xx))
  (empty (tuple21 int int))))))) (mem1 v_OBF__ssdd (mk 0 v_OBF__wwdd))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__ttdd)
  (infix_plmngt int int (t2tb2 (mk 1 v_OBF__wwdd)) (t2tb2 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__ttdd))
  (t2tb2 (mk 1 v_OBF__wwdd)))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__uudd)
  (infix_plmngt int int (t2tb2 (mk 1 v_OBF__wwdd)) (t2tb2 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__uudd))
  (t2tb2 (mk 1 v_OBF__wwdd)))) (mem1 v_OBF__yydd integer)) (mem1 v_OBF__xx
  integer)) (mem (tuple21 (tuple21 int enum_OBF__aa1) int)
  (Tuple2 (tuple21 int enum_OBF__aa1) int
  (Tuple2 int enum_OBF__aa1 (t2tb3 v_OBF__yydd) (t2tb5 v_OBF__zzdd))
  (t2tb3 v_OBF__xx)) (t2tb10 v_OBF__aaee))) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__nndd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb17 v_OBF__oodd)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (t2tb2 v_OBF__ppdd))))) (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__qqdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__vvdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb16 v_OBF__xxdd)
  (power (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb12 v_OBF__bbee)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__nndd) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ggbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb17 v_OBF__oodd)
  (add int (t2tb3 v_OBF__hhbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__qqdd) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__vvdd) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ccee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb16 v_OBF__xxdd) (t2tb2 v_OBF__ppdd))
  (add int (t2tb3 v_OBF__ddee) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (t2tb2 v_OBF__ppdd)) (add int (t2tb3 v_OBF__eeee) (empty int)))))) (mem1
  v_OBF__ddbb integer)) (mem1 v_OBF__tt v_OBF__cccc)) (mem1 v_OBF__vv
  v_OBF__bbbb)) (mem1 v_OBF__kkbb v_OBF__ppdd)) (mem1 v_OBF__eebb
  v_OBF__dddd)) (mem (set1 (tuple21 (tuple21 (tuple21 int int) int) int))
  (t2tb12 v_OBF__bbee)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb2 v_OBF__cccc) (t2tb2 v_OBF__bbbb))
  (t2tb2 v_OBF__ppdd)) (t2tb2 v_OBF__dddd)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb2 v_OBF__eedd)
  (inter int (t2tb2 v_OBF__jjbb)
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int)))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq 
  int (image int int (t2tb16 v_OBF__ttcc) (t2tb2 v_OBF__zz))
  (image int int (t2tb16 v_OBF__jjdd)
  (add int (t2tb3 v_OBF__tt) (empty int))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq 
  int (t2tb2 v_OBF__ww)
  (image int int (t2tb16 v_OBF__iidd)
  (add int (t2tb3 v_OBF__tt) (empty int)))))) (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb16 v_OBF__jjdd)
  (range_substraction int int (t2tb16 v_OBF__iidd)
  (image int int
  (times int int (add int (t2tb3 0) (empty int))
  (diff int (t2tb2 v_OBF__yy) (add int (t2tb3 v_OBF__vv) (empty int))))
  (add int (t2tb3 1) (empty int))))) (t2tb16 v_OBF__iidd))) (infix_eqeq
  (tuple21 int int)
  (union (tuple21 int int) (t2tb16 v_OBF__jjdd)
  (range_substraction int int (t2tb16 v_OBF__iidd)
  (image int int
  (times int int (add int (t2tb3 0) (empty int))
  (diff int (t2tb2 v_OBF__yy) (add int (t2tb3 v_OBF__vv) (empty int))))
  (add int (t2tb3 0) (empty int)))))
  (union (tuple21 int int) (t2tb16 v_OBF__jjdd)
  (range_substraction int int (t2tb16 v_OBF__iidd)
  (diff int (t2tb2 v_OBF__yy) (add int (t2tb3 v_OBF__vv) (empty int)))))))
  (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb16 v_OBF__ggee)
  (range_substraction int int (t2tb16 v_OBF__hhee)
  (image int int
  (times int int (add int (t2tb3 0) (empty int))
  (diff int (t2tb2 v_OBF__iiee) (add int (t2tb3 v_OBF__ssbb) (empty int))))
  (add int (t2tb3 1) (empty int))))) (t2tb16 v_OBF__hhee))) (mem1 v_OBF__xx
  (tb2t2
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int))))))
  (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb10 v_OBF__aaee)
  (infix_plmngt int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int)))
  (t2tb4 set_enum_OBF__aa))
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int))))))
  (infix_eqeq (tuple21 int enum_OBF__aa1)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb10 v_OBF__aaee))
  (times enum_OBF__aa1 int
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int)))
  (t2tb4 set_enum_OBF__aa)))) (= v_OBF__jjee v_OBF__ddbb))
  (= v_OBF__kkee v_OBF__tt)) (= v_OBF__llee v_OBF__vv))
  (= v_OBF__mmee v_OBF__kkbb)) (= v_OBF__nnee v_OBF__eebb))
  (= v_OBF__ooee v_OBF__ffee)) (= v_OBF__ppee v_OBF__xx))
  (= v_OBF__qqee v_OBF__rrdd)) (= v_OBF__rree v_OBF__ssdd)) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__ssee) (t2tb16 v_OBF__ttdd))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__ttee) (t2tb16 v_OBF__uudd)))
  (= v_OBF__uuee v_OBF__yybb)) (infix_eqeq int (t2tb2 v_OBF__vvee)
  (t2tb2 v_OBF__ttbb))) (infix_eqeq int (t2tb2 v_OBF__wwee)
  (t2tb2 v_OBF__yy))) (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__xxee)
  (t2tb16 v_OBF__ttcc))) (infix_eqeq (tuple21 int int) (t2tb16 v_OBF__yyee)
  (t2tb16 v_OBF__iicc))) (infix_eqeq int (t2tb2 v_OBF__zzee)
  (t2tb2 v_OBF__jjbb))) (infix_eqeq int (t2tb2 v_OBF__aaff)
  (t2tb2 v_OBF__eedd))) (infix_eqeq int (t2tb2 v_OBF__bbff)
  (t2tb2 v_OBF__ww))) (infix_eqeq int (t2tb2 v_OBF__ccff) (t2tb2 v_OBF__zz)))
  (infix_eqeq int (t2tb2 v_OBF__ddff) (t2tb2 v_OBF__ffdd))) (infix_eqeq
  enum_OBF__ii1 (t2tb6 v_OBF__eeff) (t2tb6 v_OBF__uubb))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__ffff) (t2tb16 v_OBF__qqcc))) (infix_eqeq
  (tuple21 int int) (t2tb16 v_OBF__ggff) (t2tb16 v_OBF__sscc))) (infix_eqeq
  (tuple21 int bool) (t2tb14 v_OBF__hhff) (t2tb14 v_OBF__ppcc))))))

(declare-fun f3 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f3_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f3 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and (infix_eqeq int (t2tb2 v_OBF__oocc)
  (inter int (t2tb2 v_OBF__yycc)
  (image int int (inverse int int (t2tb16 v_OBF__ttcc))
  (union int (add int (t2tb3 v_OBF__vv) (empty int))
  (add int (t2tb3 v_OBF__uucc) (empty int)))))) (= v_OBF__ddbb 1))
  (infix_eqeq int (t2tb2 v_OBF__zzcc)
  (inter int
  (inter int
  (image int bool (inverse bool int (t2tb14 v_OBF__ppcc))
  (add bool (t2tb true) (empty bool)))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__rrcc)))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc))))
  (add int (t2tb3 v_OBF__tt) (empty int)))))) (infix_eqeq int
  (t2tb2 v_OBF__yycc)
  (inter int (t2tb2 v_OBF__zzcc)
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int)))))) (infix_eqeq int
  (t2tb2 v_OBF__xxcc)
  (image int int (t2tb16 v_OBF__ttcc) (t2tb2 v_OBF__yycc)))) (infix_eqeq 
  int (t2tb2 v_OBF__vvcc)
  (inter int (t2tb2 v_OBF__yycc)
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__wwcc)))
  (add int (t2tb3 v_OBF__tt) (empty int)))))))))

(declare-fun f5 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f5_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f5 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq int (t2tb2 v_OBF__yycc)
  (inter int
  (inter int
  (inter int
  (image int bool (inverse bool int (t2tb14 v_OBF__ppcc))
  (add bool (t2tb true) (empty bool)))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__rrcc)))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc))))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int))))))))

(declare-fun f7 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f7_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f7 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq int (t2tb2 v_OBF__xxcc)
  (image int int (t2tb16 v_OBF__ttcc)
  (inter int
  (inter int
  (inter int
  (image int bool (inverse bool int (t2tb14 v_OBF__ppcc))
  (add bool (t2tb true) (empty bool)))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__rrcc)))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc))))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int)))))))))

(declare-fun f9 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f9_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f9 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq int (t2tb2 v_OBF__vvcc)
  (inter int
  (inter int
  (inter int
  (inter int
  (image int bool (inverse bool int (t2tb14 v_OBF__ppcc))
  (add bool (t2tb true) (empty bool)))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__rrcc)))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc))))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int))))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__wwcc)))
  (add int (t2tb3 v_OBF__tt) (empty int))))))))

(declare-fun f11 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f11_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f11 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq int (t2tb2 v_OBF__oocc)
  (inter int
  (inter int
  (inter int
  (inter int
  (image int bool (inverse bool int (t2tb14 v_OBF__ppcc))
  (add bool (t2tb true) (empty bool)))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__qqcc) (t2tb16 v_OBF__rrcc)))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int
  (inverse int int
  (semicolon int int int (t2tb16 v_OBF__sscc)
  (inverse int int (t2tb16 v_OBF__rrcc))))
  (add int (t2tb3 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__iicc))
  (add int (t2tb3 v_OBF__eebb) (empty int))))
  (image int int (inverse int int (t2tb16 v_OBF__ttcc))
  (union int (add int (t2tb3 v_OBF__vv) (empty int))
  (add int (t2tb3 v_OBF__uucc) (empty int)))))))))

(declare-fun f12 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f12_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f12 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__kkcc) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__llcc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__llcc)) (t2tb2 v_OBF__bbcc)))
  (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__mmcc)
  (relation int int (t2tb2 v_OBF__bbcc)
  (union int
  (union int (add int (t2tb3 v_OBF__ggbb) (empty int))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (add int (t2tb3 v_OBF__ffbb) (empty int)))))) (mem
  (set1 (tuple21 int bool)) (t2tb14 v_OBF__nncc)
  (infix_plmngt bool int (t2tb2 v_OBF__bbcc) (t2tb1 b_bool)))) (infix_eqeq
  int (dom bool int (t2tb14 v_OBF__nncc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f15 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f15_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f15 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__jjcc) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__ggcc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__ggcc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f16 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f16_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f16 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (mem (set1 (tuple21 int int)) (t2tb16 v_OBF__iicc)
  (relation int int (t2tb2 v_OBF__bbcc)
  (union int
  (union int (add int (t2tb3 v_OBF__ggbb) (empty int))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))))))

(declare-fun f17 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f17_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f17 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__hhcc) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__ggcc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__ggcc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f18 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f18_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f18 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__ffcc) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__ggcc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__ggcc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f19 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f19_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f19 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__eecc) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__aacc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__aacc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f20 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f20_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f20 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__ddcc) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__aacc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__aacc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f21 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f21_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f21 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__tt v_OBF__zzbb) (mem (set1 (tuple21 int int))
  (t2tb16 v_OBF__aacc)
  (infix_plmngt int int (t2tb2 v_OBF__bbcc) (t2tb2 v_OBF__cccc))))
  (infix_eqeq int (dom int int (t2tb16 v_OBF__aacc)) (t2tb2 v_OBF__bbcc)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__vv v_OBF__ssbb))
  (= v_OBF__yybb false)))))

(declare-fun f22 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f22_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f22 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb2 v_OBF__vvbb) (power int (t2tb2 v_OBF__bbbb)))
  (mem (set1 int) (t2tb2 v_OBF__wwbb) (power int (t2tb2 v_OBF__bbbb))))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__tt v_OBF__xxbb))
  (= v_OBF__vv v_OBF__ssbb)) (= v_OBF__yybb false)))))

(declare-fun f23 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f23_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f23 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and (and (mem1 v_OBF__vv v_OBF__ttbb) (= v_OBF__ddbb 2))
  (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__tt v_OBF__oobb))
  (= v_OBF__kkbb v_OBF__llbb)))))

(declare-fun f24 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f24_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f24 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (mem1 v_OBF__tt
  (tb2t2
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int))))))))

(declare-fun f25 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f25_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f25 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (mem (set1 enum_OBF__ii1)
  (diff enum_OBF__ii1 (t2tb6 v_OBF__uubb)
  (union enum_OBF__ii1
  (union enum_OBF__ii1
  (union enum_OBF__ii1
  (union enum_OBF__ii1
  (union enum_OBF__ii1
  (union enum_OBF__ii1
  (union enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb7 E_OBF__qq) (empty enum_OBF__ii1))
  (add enum_OBF__ii1 (t2tb7 E_OBF__pp) (empty enum_OBF__ii1)))
  (add enum_OBF__ii1 (t2tb7 E_OBF__oo) (empty enum_OBF__ii1)))
  (add enum_OBF__ii1 (t2tb7 E_OBF__nn) (empty enum_OBF__ii1)))
  (add enum_OBF__ii1 (t2tb7 E_OBF__mm) (empty enum_OBF__ii1)))
  (add enum_OBF__ii1 (t2tb7 E_OBF__ll) (empty enum_OBF__ii1)))
  (add enum_OBF__ii1 (t2tb7 E_OBF__kk) (empty enum_OBF__ii1)))
  (add enum_OBF__ii1 (t2tb7 E_OBF__jj) (empty enum_OBF__ii1))))
  (power enum_OBF__ii1 (t2tb6 v_OBF__uubb))))))

(declare-fun f26 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f26_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f26 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and (and (mem1 v_OBF__vv v_OBF__ttbb) (= v_OBF__ddbb 2))
  (= v_OBF__eebb v_OBF__hhbb)) (= v_OBF__tt v_OBF__ppbb))
  (= v_OBF__kkbb v_OBF__llbb)))))

(declare-fun f27 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f27_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f27 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (mem (set1 enum_OBF__ii1)
  (diff enum_OBF__ii1 (t2tb6 v_OBF__uubb)
  (union enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb7 E_OBF__ss) (empty enum_OBF__ii1))
  (add enum_OBF__ii1 (t2tb7 E_OBF__rr) (empty enum_OBF__ii1))))
  (power enum_OBF__ii1 (t2tb6 v_OBF__uubb))))))

(declare-fun f28 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f28_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f28 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__eebb
  (tb2t2
  (union int (add int (t2tb3 v_OBF__ggbb) (empty int))
  (add int (t2tb3 v_OBF__hhbb) (empty int))))) (mem1 v_OBF__tt
  (tb2t2
  (union int (union int (t2tb2 v_OBF__mmbb) (t2tb2 v_OBF__nnbb))
  (union int
  (union int
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int)))
  (add int (t2tb3 v_OBF__qqbb) (empty int)))
  (add int (t2tb3 v_OBF__rrbb) (empty int)))))))
  (=> (mem1 v_OBF__tt v_OBF__mmbb) (not (= v_OBF__vv v_OBF__ssbb))))
  (=> (mem1 v_OBF__tt v_OBF__nnbb) (not (mem1 v_OBF__vv v_OBF__ttbb))))
  (=>
  (and (mem1 v_OBF__tt
  (tb2t2
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int))))) (mem1 v_OBF__vv v_OBF__ttbb))
  (and (= v_OBF__eebb v_OBF__hhbb) (not (= v_OBF__kkbb v_OBF__llbb)))))
  (=> (= v_OBF__tt v_OBF__qqbb) (= v_OBF__eebb v_OBF__hhbb)))
  (=> (= v_OBF__tt v_OBF__rrbb) (not (= v_OBF__vv v_OBF__ssbb))))
  (= v_OBF__ddbb 2)) (mem1 v_OBF__tt
  (tb2t2
  (union int (add int (t2tb3 v_OBF__oobb) (empty int))
  (add int (t2tb3 v_OBF__ppbb) (empty int)))))) (mem1 v_OBF__vv v_OBF__ttbb)))))

(declare-fun f30 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f30_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f30 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (not (= v_OBF__kkbb v_OBF__llbb)))))

(declare-fun f33 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f33_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f33 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_OBF__eebb
  (tb2t2
  (union int
  (union int (add int (t2tb3 v_OBF__ggbb) (empty int))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (add int (t2tb3 v_OBF__ffbb) (empty int))))) (mem1 v_OBF__tt v_OBF__uu))
  (=> (and (= v_OBF__eebb v_OBF__ggbb) (mem1 v_OBF__tt v_OBF__iibb))
  (not (= v_OBF__xx 1)))) (= v_OBF__ddbb 2)) (infix_eqeq int
  (t2tb2 v_OBF__jjbb) (empty int))) (mem1 v_OBF__tt v_OBF__iibb))
  (= v_OBF__eebb v_OBF__ggbb)))))

(declare-fun f34 ((set (tuple2 Int Int)) (set Int) enum_OBF__aa (set Int)
  (set Int) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set Int) Bool (set Int) (set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int Int
  (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int)) (set Int)
  (set Int) (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set Int)
  Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) Int
  (set enum_OBF__ii) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int (set (tuple2 Int Int)) Int (set Int) (set (tuple2 Int Bool)) Int
  (set (tuple2 Int Int)) Bool (set (tuple2 (tuple2 Int Int) Int)) (set Int)
  Int (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Bool)) (set Int)
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set Int) (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int (set (tuple2 Int Bool)) Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) Int (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Bool)) (set (tuple2 Int
  Int)) (set (tuple2 Int Int)) (set Int) Int (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  Bool (set Int) (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set enum_OBF__ii) Int (set Int) (set Int) Int (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set Int) Int (set Int) (set Int) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set Int)
  (set Int) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int))
  (set Int) (set Int) (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) Int) Bool)

;; f34_def
  (assert
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
  (= (f34 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (not (= v_OBF__xx 1)))))

(assert
;; OBF__kkgg_1
 ;; File "POwhy_bpo2why/p9/p9_11.why", line 5215, characters 7-18
  (not
  (forall ((v_OBF__zzff (set (tuple2 Int Int))) (v_OBF__zzee (set Int))
  (v_OBF__zzdd enum_OBF__aa) (v_OBF__zzcc (set Int)) (v_OBF__zzbb (set Int))
  (v_OBF__zz (set Int)) (v_OBF__yyff (set (tuple2 Int Int)))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int)
  (v_OBF__yycc (set Int)) (v_OBF__yybb Bool) (v_OBF__yy (set Int))
  (v_OBF__xxff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__xxee (set (tuple2 Int Int))) (v_OBF__xxdd (set (tuple2 Int Int)))
  (v_OBF__xxcc (set Int)) (v_OBF__xxbb Int) (v_OBF__xx Int)
  (v_OBF__wwff (set (tuple2 Int Int))) (v_OBF__wwee (set Int))
  (v_OBF__wwdd Int) (v_OBF__wwcc (set (tuple2 Int Int)))
  (v_OBF__wwbb (set Int)) (v_OBF__ww (set Int)) (v_OBF__vvff (set Int))
  (v_OBF__vvee (set Int)) (v_OBF__vvdd (set (tuple2 Int Int)))
  (v_OBF__vvcc (set Int)) (v_OBF__vvbb (set Int)) (v_OBF__vv Int)
  (v_OBF__uuff (set (tuple2 Int Int))) (v_OBF__uuee Bool)
  (v_OBF__uudd (set (tuple2 Int Int))) (v_OBF__uucc Int)
  (v_OBF__uubb (set enum_OBF__ii)) (v_OBF__uu (set Int))
  (v_OBF__ttff (set (tuple2 Int Int))) (v_OBF__ttee (set (tuple2 Int Int)))
  (v_OBF__ttdd (set (tuple2 Int Int))) (v_OBF__ttcc (set (tuple2 Int Int)))
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssff (set (tuple2 Int
  Int))) (v_OBF__ssee (set (tuple2 Int Int))) (v_OBF__ssdd Int)
  (v_OBF__sscc (set (tuple2 Int Int))) (v_OBF__ssbb Int)
  (v_OBF__rrff (set (tuple2 Int Int))) (v_OBF__rree Int) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set (tuple2 Int Int))) (v_OBF__rrbb Int)
  (v_OBF__qqff (set (tuple2 Int Int))) (v_OBF__qqee Int)
  (v_OBF__qqdd (set (tuple2 Int Int))) (v_OBF__qqcc (set (tuple2 Int Int)))
  (v_OBF__qqbb Int) (v_OBF__ppff (set (tuple2 Int Int))) (v_OBF__ppee Int)
  (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int Bool)))
  (v_OBF__ppbb Int) (v_OBF__ooff (set (tuple2 Int Int))) (v_OBF__ooee Bool)
  (v_OBF__oodd (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__oocc (set Int))
  (v_OBF__oobb Int) (v_OBF__nnff (set Int)) (v_OBF__nnee Int)
  (v_OBF__nndd (set (tuple2 Int Int))) (v_OBF__nncc (set (tuple2 Int Bool)))
  (v_OBF__nnbb (set Int)) (v_OBF__mmff (set (tuple2 Int Int)))
  (v_OBF__mmee Int) (v_OBF__mmdd (set (tuple2 Int Int)))
  (v_OBF__mmcc (set (tuple2 Int Int))) (v_OBF__mmbb (set Int))
  (v_OBF__llff (set (tuple2 Int Int))) (v_OBF__llee Int)
  (v_OBF__lldd (set (tuple2 Int Int))) (v_OBF__llcc (set (tuple2 Int Int)))
  (v_OBF__llbb Int) (v_OBF__kkff (set (tuple2 Int Bool))) (v_OBF__kkee Int)
  (v_OBF__kkdd (set (tuple2 Int Int))) (v_OBF__kkcc (set Int))
  (v_OBF__kkbb Int) (v_OBF__jjff (set (tuple2 Int Int))) (v_OBF__jjee Int)
  (v_OBF__jjdd (set (tuple2 Int Int))) (v_OBF__jjcc (set Int))
  (v_OBF__jjbb (set Int)) (v_OBF__iiff (set (tuple2 Int Int)))
  (v_OBF__iiee (set Int)) (v_OBF__iidd (set (tuple2 Int Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb (set Int))
  (v_OBF__hhff (set (tuple2 Int Bool))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 Int Int))) (v_OBF__hhcc (set Int))
  (v_OBF__hhbb Int) (v_OBF__ggff (set (tuple2 Int Int)))
  (v_OBF__ggee (set (tuple2 Int Int))) (v_OBF__ggdd (set (tuple2 Int Int)))
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb Int)
  (v_OBF__ffgg (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__ffff (set (tuple2 Int Int))) (v_OBF__ffee Bool)
  (v_OBF__ffdd (set Int)) (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int)
  (v_OBF__eegg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__eeff (set enum_OBF__ii)) (v_OBF__eeee Int) (v_OBF__eedd (set Int))
  (v_OBF__eecc (set Int)) (v_OBF__eebb Int)
  (v_OBF__ddgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ddff (set Int)) (v_OBF__ddee Int) (v_OBF__dddd (set Int))
  (v_OBF__ddcc (set Int)) (v_OBF__ddbb Int)
  (v_OBF__ccgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccff (set Int)) (v_OBF__ccee Int) (v_OBF__ccdd (set Int))
  (v_OBF__cccc (set Int)) (v_OBF__ccbb Int)
  (v_OBF__bbgg (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__bbff (set Int)) (v_OBF__bbee (set (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aagg (set (tuple2 Int Int)))
  (v_OBF__aaff (set Int)) (v_OBF__aaee (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__aadd (set (tuple2 Int Int))) (v_OBF__aacc (set (tuple2 Int
  Int))) (v_OBF__aabb Int))
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
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
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffgg v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb
  v_OBF__eegg v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb
  v_OBF__ddgg v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb
  v_OBF__ccgg v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb
  v_OBF__bbgg v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aagg v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (f18 v_OBF__zzff v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
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
  v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff v_OBF__kkee
  v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee v_OBF__jjdd
  v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc
  v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffgg
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eegg
  v_OBF__eeff v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddgg
  v_OBF__ddff v_OBF__ddee v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccgg
  v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc v_OBF__ccbb v_OBF__bbgg
  v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb v_OBF__aagg
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb))) (mem1
  v_OBF__tt v_OBF__mmbb)))))
(check-sat)
