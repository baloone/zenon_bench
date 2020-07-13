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

(declare-sort enum_OBF__aa 0)

(declare-fun enum_OBF__aa1 () ty)

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (Int (set Int)) Bool)

(declare-fun mem2 ((tuple2 (tuple2 Int enum_OBF__aa) Int)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun t2tb ((set (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb x))))

(declare-fun tb2t (uni) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni)) (! (= (t2tb (tb2t j)) j) :pattern ((t2tb (tb2t j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (infix_eqeq (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1)
  (t2tb s2))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (= (mem2 x s1) (mem2 x s2))))))

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
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1) (t2tb s2))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem2 x s1) (mem2 x s2))))))

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

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (is_empty (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))) (not (mem2 x s))))))

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
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (not (mem2 x (tb2t (empty (tuple21 (tuple21 int enum_OBF__aa1) int)))))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem1 x (tb2t1 (empty int))))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun t2tb2 ((tuple2 (tuple2 Int enum_OBF__aa) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))) (sort
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x))))

(declare-fun tb2t2 (uni) (tuple2 (tuple2 Int enum_OBF__aa) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb2 (tb2t2 j)) j) :pattern ((t2tb2 (tb2t2 j))) )))

;; add_def1
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem2 x
  (tb2t (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 y) (t2tb s))))
  (or (= x y) (mem2 x s))))))

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
  (= (mem1 x (tb2t1 (add int (t2tb3 y) (t2tb1 s)))) (or (= x y) (mem1 x s))))))

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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem2 x
  (tb2t
  (remove (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 y) (t2tb s))))
  (and (not (= x y)) (mem2 x s)))))

;; remove_def1
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem1 x (tb2t1 (remove int (t2tb3 y) (t2tb1 s))))
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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (mem2 x s)
  (= (tb2t
     (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x)
     (remove (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem1 x s)
  (= (tb2t1 (add int (t2tb3 x) (remove int (t2tb3 x) (t2tb1 s)))) s))))

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
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (= (mem2 x
  (tb2t
  (union (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1) (t2tb s2))))
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
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (= (mem2 x
  (tb2t
  (inter (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1) (t2tb s2))))
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
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (= (mem2 x
  (tb2t (diff (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1) (t2tb s2))))
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
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (not (is_empty (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)))
  (mem2 (tb2t2 (choose (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)))
  s))))

;; choose_def
  (assert
  (forall ((s (set Int)))
  (=> (not (is_empty int (t2tb1 s))) (mem1 (tb2t3 (choose int (t2tb1 s))) s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))) (mem2 x
  (tb2t (all (tuple21 (tuple21 int enum_OBF__aa1) int))))))

;; all_def
  (assert (forall ((x Int)) (mem1 x (tb2t1 (all int)))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

(declare-fun t2tb4 (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb4 x))))

(declare-fun tb2t4 (uni) Bool)

;; BridgeL
  (assert
  (forall ((i Bool)) (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb4 (tb2t4 j)) j)) :pattern ((t2tb4 (tb2t4 j))) )))

(declare-fun t2tb5 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb5 x))))

(declare-fun tb2t5 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool))) (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb5 (tb2t5 j)) j)) :pattern ((t2tb5
                                                                 (tb2t5 j))) )))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb4 x) (t2tb5 b_bool))))

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
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t1 (empty int))))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t1 (add int (t2tb3 b) (t2tb1 (mk a (- b 1)))))))))

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

(declare-fun Tuple2 (ty ty uni uni) uni)

;; Tuple2_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni) (x1 uni)) (sort (tuple21 a1 a) (Tuple2 a1 a x x1)))))

(declare-fun Tuple21 (Int enum_OBF__aa) (tuple2 Int enum_OBF__aa))

(declare-fun Tuple22 ((tuple2 Int enum_OBF__aa) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))

(declare-fun Tuple2_proj_1 (ty ty uni) uni)

;; Tuple2_proj_1_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni)) (sort a1 (Tuple2_proj_1 a1 a x)))))

(declare-fun t2tb6 ((tuple2 Int enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa))) (sort (tuple21 int enum_OBF__aa1)
  (t2tb6 x))))

(declare-fun tb2t6 (uni) (tuple2 Int enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int enum_OBF__aa)))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb6 (tb2t6 j)) j) :pattern ((t2tb6 (tb2t6 j))) )))

;; Tuple2_proj_1_def
  (assert
  (forall ((u Int) (u1 enum_OBF__aa))
  (= (tb2t3 (Tuple2_proj_1 int enum_OBF__aa1 (t2tb6 (Tuple21 u u1)))) u)))

;; Tuple2_proj_1_def
  (assert
  (forall ((u (tuple2 Int enum_OBF__aa)) (u1 Int))
  (= (tb2t6
     (Tuple2_proj_1 (tuple21 int enum_OBF__aa1) int (t2tb2 (Tuple22 u u1)))) u)))

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

(declare-fun t2tb7 (enum_OBF__aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__aa)) (sort enum_OBF__aa1 (t2tb7 x))))

(declare-fun tb2t7 (uni) enum_OBF__aa)

;; BridgeL
  (assert
  (forall ((i enum_OBF__aa))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__aa1 j) (= (t2tb7 (tb2t7 j)) j)) :pattern ((t2tb7
                                                                   (tb2t7 j))) )))

;; Tuple2_proj_2_def
  (assert
  (forall ((u Int) (u1 enum_OBF__aa))
  (= (tb2t7 (Tuple2_proj_2 int enum_OBF__aa1 (t2tb6 (Tuple21 u u1)))) u1)))

;; Tuple2_proj_2_def
  (assert
  (forall ((u (tuple2 Int enum_OBF__aa)) (u1 Int))
  (= (tb2t3
     (Tuple2_proj_2 (tuple21 int enum_OBF__aa1) int (t2tb2 (Tuple22 u u1)))) u1)))

;; Tuple2_proj_2_def
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((u uni) (u1 uni))
  (=> (sort a u1) (= (Tuple2_proj_2 a1 a (Tuple2 a1 a u u1)) u1)))))

;; tuple2_inversion
  (assert
  (forall ((u (tuple2 Int enum_OBF__aa)))
  (= u (Tuple21 (tb2t3 (Tuple2_proj_1 int enum_OBF__aa1 (t2tb6 u)))
       (tb2t7 (Tuple2_proj_2 int enum_OBF__aa1 (t2tb6 u)))))))

;; tuple2_inversion
  (assert
  (forall ((u (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (= u (Tuple22
       (tb2t6 (Tuple2_proj_1 (tuple21 int enum_OBF__aa1) int (t2tb2 u)))
       (tb2t3 (Tuple2_proj_2 (tuple21 int enum_OBF__aa1) int (t2tb2 u)))))))

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
  (forall ((f uni) (s uni) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (and
  (=> (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (relation (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (=>
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) f)
  (and (mem a x s) (mem2 y t))))) (mem
  (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (relation (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (relation int a s (t2tb1 t)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f)
  (and (mem a x s) (mem1 y t))))) (mem (set1 (tuple21 a int)) f
  (relation int a s (t2tb1 t))))))))

(declare-fun t2tb8 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))) (t2tb8 x))))

(declare-fun tb2t8 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) (tuple2 (tuple2 Int enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb8 (tb2t8 j)) j) :pattern ((t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb9 x))))

(declare-fun tb2t9 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb9 (tb2t9 j)) j) :pattern ((t2tb9 (tb2t9 j))) )))

(declare-fun t2tb10 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb10 x))))

(declare-fun tb2t10 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb10 (tb2t10 j)) j) :pattern ((t2tb10 (tb2t10 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (s (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb9 f)
  (relation (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb t)))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y)) (t2tb9 f))
  (and (mem2 x s) (mem2 y t)))))))

(declare-fun t2tb11 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)))
  (t2tb11 x))))

(declare-fun tb2t11 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))))) (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb11 (tb2t11 j)) j) :pattern ((t2tb11 (tb2t11 j))) )))

(declare-fun t2tb12 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))))
  (sort (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int) (t2tb13 x))))

(declare-fun tb2t13 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb13 (tb2t13 j)) j) :pattern ((t2tb13 (tb2t13 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t (set Int)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (t2tb12 f)
  (relation int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb1 t)))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y Int))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y))
  (t2tb12 f)) (and (mem2 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (relation b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (=>
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) f)
  (and (mem2 x s) (mem b y t))))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (relation b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t)))))))

(declare-fun t2tb14 ((set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

(declare-fun t2tb15 ((set (tuple2 Int enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int enum_OBF__aa)))) (sort
  (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (tuple2 Int enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int enum_OBF__aa))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)))
  (= (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (relation int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t)))
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (=> (mem2 (Tuple22 x y) f)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 s)) (mem1 y t)))))))

(declare-fun t2tb16 ((set (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (set (tuple2 Int (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))))) (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb16 (tb2t16 j)) j) :pattern ((t2tb16 (tb2t16 j))) )))

(declare-fun t2tb17 ((set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (sort (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

(declare-fun t2tb18 ((tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb18 x))))

(declare-fun tb2t18 (uni) (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb18 (tb2t18 j)) j) :pattern ((t2tb18 (tb2t18 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (s (set Int)) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb17 f)
  (relation (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 s) (t2tb t)))
  (forall ((x Int) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y))
  (t2tb17 f)) (and (mem1 x s) (mem2 y t)))))))

(declare-fun t2tb19 ((set (set (tuple2 Int enum_OBF__aa)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int enum_OBF__aa))))) (sort
  (set1 (set1 (tuple21 int enum_OBF__aa1))) (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (set (tuple2 Int enum_OBF__aa))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int enum_OBF__aa)))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

(declare-fun t2tb20 ((set enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__aa))) (sort (set1 enum_OBF__aa1) (t2tb20 x))))

(declare-fun tb2t20 (uni) (set enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__aa)))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__aa1) j) (= (t2tb20 (tb2t20 j)) j)) :pattern (
  (t2tb20 (tb2t20 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)))
  (= (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (relation enum_OBF__aa1 int (t2tb1 s) (t2tb20 t)))
  (forall ((x Int) (y enum_OBF__aa))
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 f))
  (and (mem1 x s) (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 t))))))))

(declare-fun t2tb21 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb21 (tb2t21 j)) j) :pattern ((t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb22 x))))

(declare-fun tb2t22 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb22 (tb2t22 j)) j) :pattern ((t2tb22 (tb2t22 j))) )))

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
  (= (mem (set1 (tuple21 int int)) (t2tb22 f)
  (relation int int (t2tb1 s) (t2tb1 t)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb22 f))
  (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (relation b int (t2tb1 s) t))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) f)
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
  (forall ((r uni) (dom uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (and
     (=> (mem2 y
     (tb2t (image (tuple21 (tuple21 int enum_OBF__aa1) int) a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem
     (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem
     (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r)))
     (mem2 y
     (tb2t (image (tuple21 (tuple21 int enum_OBF__aa1) int) a r dom))))) :pattern ((mem2
  y (tb2t (image (tuple21 (tuple21 int enum_OBF__aa1) int) a r dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y Int))
  (! (and
     (=> (mem1 y (tb2t1 (image int a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)))
     (mem1 y (tb2t1 (image int a r dom))))) :pattern ((mem1
  y (tb2t1 (image int a r dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (dom (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (mem2 y
     (tb2t
     (image (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 r) (t2tb dom))))
     (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y))
     (t2tb9 r))))) :pattern ((mem2
  y
  (tb2t
  (image (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (dom (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (y Int))
  (! (= (mem1 y
     (tb2t1
     (image int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 r)
     (t2tb dom))))
     (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x)
     (t2tb3 y)) (t2tb12 r))))) :pattern ((mem1
  y
  (tb2t1
  (image int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (y uni))
  (! (= (mem b y
     (image b (tuple21 (tuple21 int enum_OBF__aa1) int) r (t2tb dom)))
     (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) r)))) :pattern ((mem
  b y (image b (tuple21 (tuple21 int enum_OBF__aa1) int) r (t2tb dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (dom (set (tuple2 Int enum_OBF__aa))) (y Int))
  (! (= (mem1 y
     (tb2t1 (image int (tuple21 int enum_OBF__aa1) (t2tb r) (t2tb15 dom))))
     (exists ((x (tuple2 Int enum_OBF__aa)))
     (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 dom)) (mem2
     (Tuple22 x y) r)))) :pattern ((mem1
  y
  (tb2t1 (image int (tuple21 int enum_OBF__aa1) (t2tb r) (t2tb15 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (dom (set Int)) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (mem2 y
     (tb2t
     (image (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 r)
     (t2tb1 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem
     (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x)
     (t2tb2 y)) (t2tb17 r))))) :pattern ((mem2
  y
  (tb2t
  (image (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 r)
  (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int enum_OBF__aa))) (dom (set Int))
  (y enum_OBF__aa))
  (! (= (mem enum_OBF__aa1 (t2tb7 y)
     (image enum_OBF__aa1 int (t2tb15 r) (t2tb1 dom)))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
     (t2tb15 r))))) :pattern ((mem
  enum_OBF__aa1 (t2tb7 y)
  (image enum_OBF__aa1 int (t2tb15 r) (t2tb1 dom)))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom (set Int)) (y Int))
  (! (= (mem1 y (tb2t1 (image int int (t2tb22 r) (t2tb1 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int int)
     (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb22 r))))) :pattern ((mem1
  y (tb2t1 (image int int (t2tb22 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (y uni))
  (! (= (mem b y (image b int r (t2tb1 dom)))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r)))) :pattern ((mem
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
  (forall ((f uni) (s uni) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (and
  (=> (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
  (and
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) f)
  (and (mem a x s) (mem2 y t))))
  (forall ((x uni) (y1 (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (y2 (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=>
  (and (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y1)) f) (mem
  (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y2)) f))
  (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (forall ((x uni) (y1 (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (y2 (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y1)) f) (mem
  (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y2)) f))
  (= y1 y2))))) (mem
  (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
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
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (s (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb9 f)
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb t)))
  (and
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y)) (t2tb9 f))
  (and (mem2 x s) (mem2 y t))))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y1 (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (y2 (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=>
  (and (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y1)) (t2tb9 f))
  (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y2)) (t2tb9 f)))
  (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t (set Int)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (t2tb12 f)
  (infix_plmngt int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)
  (t2tb1 t)))
  (and
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y Int))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y))
  (t2tb12 f)) (and (mem2 x s) (mem1 y t))))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y1))
  (t2tb12 f)) (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y2))
  (t2tb12 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (and
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) f)
  (and (mem2 x s) (mem b y t))))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y1) f) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y2) f))
  (= y1 y2)))))))
  (=>
  (and
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y1) f) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y2) f))
  (= y1 y2)))))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)))
  (= (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t)))
  (and
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (=> (mem2 (Tuple22 x y) f)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 s)) (mem1 y t))))
  (forall ((x (tuple2 Int enum_OBF__aa)) (y1 Int) (y2 Int))
  (=> (and (mem2 (Tuple22 x y1) f) (mem2 (Tuple22 x y2) f)) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (s (set Int)) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb17 f)
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 s)
  (t2tb t)))
  (and
  (forall ((x Int) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y))
  (t2tb17 f)) (and (mem1 x s) (mem2 y t))))
  (forall ((x Int) (y1 (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (y2 (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=>
  (and (mem (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y1))
  (t2tb17 f)) (mem (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y2))
  (t2tb17 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)))
  (= (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t)))
  (and
  (forall ((x Int) (y enum_OBF__aa))
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 f))
  (and (mem1 x s) (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 t)))))
  (forall ((x Int) (y1 enum_OBF__aa) (y2 enum_OBF__aa))
  (=>
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y1)) (t2tb15 f))
  (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y2)) (t2tb15 f)))
  (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb22 f)
  (infix_plmngt int int (t2tb1 s) (t2tb1 t)))
  (and
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb22 f))
  (and (mem1 x s) (mem1 y t))))
  (forall ((x Int) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y1))
  (t2tb22 f)) (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y2))
  (t2tb22 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
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
  (forall ((f uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni)
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) f) (mem2 x
  s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t)))
  (=> (mem2 (Tuple22 x y) f) (mem (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (t2tb15 s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)) (x Int) (y enum_OBF__aa))
  (=> (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t)))
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 f))
  (mem1 x s)))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (x Int) (y uni))
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
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
  (forall ((f uni) (s uni) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) f) (mem2 y
  t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (x uni) (y Int))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f) (mem1 y t))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t)))
  (=> (mem2 (Tuple22 x y) f) (mem1 y t)))))

;; range_function
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)) (x Int) (y enum_OBF__aa))
  (=> (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t)))
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 f)) (mem
  enum_OBF__aa1 (t2tb7 y) (t2tb20 t))))))

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
  (forall ((f uni) (s uni) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (u (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb u) (t2tb t))
  (=> (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
  (=>
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) f) (mem2 y
  u)))) (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (u (set Int)))
  (=> (subset int (t2tb1 u) (t2tb1 t))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 u)))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (u (set Int)))
  (=> (subset int (t2tb1 u) (t2tb1 t))
  (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t)))
  (=>
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (=> (mem2 (Tuple22 x y) f) (mem1 y u))) (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 u))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)) (u (set enum_OBF__aa)))
  (=> (subset enum_OBF__aa1 (t2tb20 u) (t2tb20 t))
  (=> (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t)))
  (=>
  (forall ((x Int) (y enum_OBF__aa))
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 f)) (mem
  enum_OBF__aa1 (t2tb7 y) (t2tb20 u)))) (mem
  (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 u))))))))

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

(declare-fun t2tb24 ((set (tuple2 Int (tuple2 Int enum_OBF__aa)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int enum_OBF__aa))))) (sort
  (set1 (tuple21 int (tuple21 int enum_OBF__aa1))) (t2tb24 x))))

(declare-fun tb2t24 (uni) (set (tuple2 Int (tuple2 Int enum_OBF__aa))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int enum_OBF__aa)))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb24 (tb2t24 j)) j) :pattern ((t2tb24 (tb2t24 j))) )))

(declare-fun t2tb25 ((tuple2 Int (tuple2 Int enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 Int enum_OBF__aa)))) (sort
  (tuple21 int (tuple21 int enum_OBF__aa1)) (t2tb25 x))))

(declare-fun tb2t25 (uni) (tuple2 Int (tuple2 Int enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 Int enum_OBF__aa))))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb25 (tb2t25 j)) j) :pattern ((t2tb25 (tb2t25 j))) )))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (= (mem (tuple21 int (tuple21 int enum_OBF__aa1))
  (Tuple2 int (tuple21 int enum_OBF__aa1) (t2tb3 y) (t2tb6 x))
  (inverse int (tuple21 int enum_OBF__aa1) (t2tb r))) (mem2 (Tuple22 x y) r)))))

(declare-fun t2tb26 ((set (tuple2 enum_OBF__aa Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__aa Int)))) (sort
  (set1 (tuple21 enum_OBF__aa1 int)) (t2tb26 x))))

(declare-fun tb2t26 (uni) (set (tuple2 enum_OBF__aa Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__aa Int))))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb26 (tb2t26 j)) j) :pattern ((t2tb26 (tb2t26 j))) )))

(declare-fun t2tb27 ((tuple2 enum_OBF__aa Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__aa Int))) (sort (tuple21 enum_OBF__aa1 int)
  (t2tb27 x))))

(declare-fun tb2t27 (uni) (tuple2 enum_OBF__aa Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__aa Int)))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb27 (tb2t27 j)) j) :pattern ((t2tb27 (tb2t27 j))) )))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 enum_OBF__aa Int))))
  (forall ((x enum_OBF__aa) (y Int))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y x))
  (inverse int enum_OBF__aa1 (t2tb26 r))) (mem (tuple21 enum_OBF__aa1 int)
  (Tuple2 enum_OBF__aa1 int (t2tb7 x) (t2tb3 y)) (t2tb26 r))))))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 Int (tuple2 Int enum_OBF__aa)))))
  (forall ((x Int) (y (tuple2 Int enum_OBF__aa)))
  (= (mem2 (Tuple22 y x)
  (tb2t (inverse (tuple21 int enum_OBF__aa1) int (t2tb24 r)))) (mem
  (tuple21 int (tuple21 int enum_OBF__aa1))
  (Tuple2 int (tuple21 int enum_OBF__aa1) (t2tb3 x) (t2tb6 y)) (t2tb24 r))))))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 Int enum_OBF__aa))))
  (forall ((x Int) (y enum_OBF__aa))
  (= (mem (tuple21 enum_OBF__aa1 int)
  (Tuple2 enum_OBF__aa1 int (t2tb7 y) (t2tb3 x))
  (inverse enum_OBF__aa1 int (t2tb15 r))) (mem (tuple21 int enum_OBF__aa1)
  (t2tb6 (Tuple21 x y)) (t2tb15 r))))))

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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (and
  (=> (mem2 x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) r))))
  (=>
  (exists ((y uni)) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) r)) (mem2
  x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) r)))))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (forall ((x (tuple2 Int enum_OBF__aa)))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb r)))
  (exists ((y Int)) (mem2 (Tuple22 x y) r))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 Int enum_OBF__aa))))
  (forall ((x Int))
  (= (mem1 x (tb2t1 (dom enum_OBF__aa1 int (t2tb15 r))))
  (exists ((y enum_OBF__aa)) (mem (tuple21 int enum_OBF__aa1)
  (t2tb6 (Tuple21 x y)) (t2tb15 r)))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x Int))
  (and
  (=> (mem1 x (tb2t1 (dom b int r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r))))
  (=> (exists ((y uni)) (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r))
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
  (forall ((y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (and
  (=> (mem2 y (tb2t (ran (tuple21 (tuple21 int enum_OBF__aa1) int) a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r))))
  (=>
  (exists ((x uni)) (mem
  (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r)) (mem2
  y (tb2t (ran (tuple21 (tuple21 int enum_OBF__aa1) int) a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y Int))
  (and
  (=> (mem1 y (tb2t1 (ran int a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r))))
  (=> (exists ((x uni)) (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r))
  (mem1 y (tb2t1 (ran int a r)))))))))

;; ran_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (forall ((y Int))
  (= (mem1 y (tb2t1 (ran int (tuple21 int enum_OBF__aa1) (t2tb r))))
  (exists ((x (tuple2 Int enum_OBF__aa))) (mem2 (Tuple22 x y) r))))))

;; ran_def
  (assert
  (forall ((r (set (tuple2 Int enum_OBF__aa))))
  (forall ((y enum_OBF__aa))
  (= (mem enum_OBF__aa1 (t2tb7 y) (ran enum_OBF__aa1 int (t2tb15 r)))
  (exists ((x Int)) (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (t2tb15 r)))))))

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
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (= (tb2t15
     (dom int (tuple21 int enum_OBF__aa1)
     (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
     (t2tb f)))) (tb2t15
                 (add (tuple21 int enum_OBF__aa1) (t2tb6 x)
                 (dom int (tuple21 int enum_OBF__aa1) (t2tb f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (x Int) (y enum_OBF__aa))
  (= (tb2t1
     (dom enum_OBF__aa1 int
     (add (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 f)))) 
  (tb2t1 (add int (t2tb3 x) (dom enum_OBF__aa1 int (t2tb15 f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (= (tb2t15
     (dom int (tuple21 int enum_OBF__aa1)
     (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
     (empty (tuple21 (tuple21 int enum_OBF__aa1) int))))) (tb2t15
                                                          (add
                                                          (tuple21 int
                                                          enum_OBF__aa1)
                                                          (t2tb6 x)
                                                          (empty
                                                          (tuple21 int
                                                          enum_OBF__aa1)))))))

;; dom_singleton
  (assert
  (forall ((x Int) (y enum_OBF__aa))
  (= (tb2t1
     (dom enum_OBF__aa1 int
     (add (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
     (empty (tuple21 int enum_OBF__aa1))))) (tb2t1
                                            (add int (t2tb3 x) (empty int))))))

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
  (forall ((s uni) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x uni)
  (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (and (mem a x s) (mem2 y t)) (mem
  (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y))
  (empty (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set Int)) (x uni) (y Int))
  (=> (and (mem a x s) (mem1 y t)) (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb3 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb1 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (and (mem2 x s) (mem2 y t)) (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t (set Int))
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y Int))
  (=> (and (mem2 x s) (mem1 y t)) (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y))
  (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)))
  (infix_plmngt int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)
  (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni)
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (and (mem2 x s) (mem b y t)) (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b))
  (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y)
  (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)))
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (=> (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 s)) (mem1 y t))
  (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
  (empty (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (x Int) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (and (mem1 x s) (mem2 y t)) (mem
  (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y))
  (empty (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 s)
  (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set enum_OBF__aa)) (x Int) (y enum_OBF__aa))
  (=> (and (mem1 x s) (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 t))) (mem
  (set1 (tuple21 int enum_OBF__aa1))
  (add (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (empty (tuple21 int enum_OBF__aa1)))
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
  (empty (tuple21 int int))) (infix_plmngt int int (t2tb1 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (x Int) (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb3 x) y) (empty (tuple21 int b)))
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
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
  (empty (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (infix_mnmngt int (tuple21 int enum_OBF__aa1)
  (add (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (empty (tuple21 int enum_OBF__aa1))) (add int (t2tb3 y) (empty int)))) :pattern (
  (tb2t
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
  (empty (tuple21 (tuple21 int enum_OBF__aa1) int))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y enum_OBF__aa)) (! (mem
  (set1 (tuple21 int enum_OBF__aa1))
  (add (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (empty (tuple21 int enum_OBF__aa1)))
  (infix_mnmngt enum_OBF__aa1 int (add int (t2tb3 x) (empty int))
  (add enum_OBF__aa1 (t2tb7 y) (empty enum_OBF__aa1)))) :pattern ((tb2t15
                                                                  (add
                                                                  (tuple21
                                                                  int
                                                                  enum_OBF__aa1)
                                                                  (t2tb6
                                                                  (Tuple21 x
                                                                  y))
                                                                  (empty
                                                                  (tuple21
                                                                  int
                                                                  enum_OBF__aa1))))) )))

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
  (forall ((f uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni)
  (a (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (mem2 a (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) f)))) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 a)
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 a))) f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (a (tuple2 Int
  enum_OBF__aa)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t))) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 a)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb f)))) (mem2
  (Tuple22 a
  (tb2t3 (apply int (tuple21 int enum_OBF__aa1) (t2tb f) (t2tb6 a)))) f))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)) (a Int))
  (=>
  (and (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t))) (mem1 a
  (tb2t1 (dom enum_OBF__aa1 int (t2tb15 f))))) (mem
  (tuple21 int enum_OBF__aa1)
  (t2tb6 (Tuple21 a (tb2t7 (apply enum_OBF__aa1 int (t2tb15 f) (t2tb3 a)))))
  (t2tb15 f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t)) (mem1
  a (tb2t1 (dom b int f)))) (mem (tuple21 int b)
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
  (forall ((f uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni)
  (a (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_mnmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (mem2 a s)) (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 a)
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 a))) f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (a (tuple2 Int
  enum_OBF__aa)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_mnmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t))) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 a) (t2tb15 s))) (mem2
  (Tuple22 a
  (tb2t3 (apply int (tuple21 int enum_OBF__aa1) (t2tb f) (t2tb6 a)))) f))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)) (a Int))
  (=>
  (and (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_mnmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t))) (mem1 a s)) (mem
  (tuple21 int enum_OBF__aa1)
  (t2tb6 (Tuple21 a (tb2t7 (apply enum_OBF__aa1 int (t2tb15 f) (t2tb3 a)))))
  (t2tb15 f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_mnmngt b int (t2tb1 s) t)) (mem1
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
  (forall ((f (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (a (tuple2 Int
  enum_OBF__aa)) (b Int))
  (=>
  (and (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb f)
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb15 s) (t2tb1 t))) (mem2
  (Tuple22 a b) f))
  (= (tb2t3 (apply int (tuple21 int enum_OBF__aa1) (t2tb f) (t2tb6 a))) b))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 Int enum_OBF__aa))) (s (set Int))
  (t (set enum_OBF__aa)) (a Int) (b enum_OBF__aa))
  (=>
  (and (mem (set1 (tuple21 int enum_OBF__aa1)) (t2tb15 f)
  (infix_plmngt enum_OBF__aa1 int (t2tb1 s) (t2tb20 t))) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 a b)) (t2tb15 f)))
  (= (tb2t7 (apply enum_OBF__aa1 int (t2tb15 f) (t2tb3 a))) b))))

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
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (= (tb2t3
     (apply int (tuple21 int enum_OBF__aa1)
     (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
     (empty (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb6 x))) y)))

;; apply_singleton
  (assert
  (forall ((x Int) (y enum_OBF__aa))
  (= (tb2t7
     (apply enum_OBF__aa1 int
     (add (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
     (empty (tuple21 int enum_OBF__aa1))) (t2tb3 x))) y)))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b))) x) y)))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))
  (! (=>
     (and (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
     (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
     (mem a x (dom (tuple21 (tuple21 int enum_OBF__aa1) int) a f))) (mem2
     (tb2t2 (apply (tuple21 (tuple21 int enum_OBF__aa1) int) a f x)) t)) :pattern ((mem
  (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
  (tb2t2 (apply (tuple21 (tuple21 int enum_OBF__aa1) int) a f x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
     (mem a x (dom int a f))) (mem1 (tb2t3 (apply int a f x)) t)) :pattern ((mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (tb2t3 (apply int a f x))) ))))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb9 f)
     (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb t))) (mem2 x
     (tb2t
     (dom (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f))))) (mem2
     (tb2t2
     (apply (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f) (t2tb2 x))) t)) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb9 f)
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb t)))
  (tb2t2
  (apply (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f) (t2tb2 x)))) )))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
     (t2tb12 f)
     (infix_plmngt int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)
     (t2tb1 t))) (mem2 x
     (tb2t (dom int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 f)))))
     (mem1
     (tb2t3
     (apply int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 f)
     (t2tb2 x))) t)) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)) (t2tb12 f)
  (infix_plmngt int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)
  (t2tb1 t)))
  (tb2t3
  (apply int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 f) (t2tb2 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (f uni)
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
     (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
     (mem2 x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) f))))
     (mem b (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 x))
     t)) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))) (s (set Int)) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (=>
     (and (mem (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
     (t2tb17 f)
     (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 s)
     (t2tb t))) (mem1 x
     (tb2t1 (dom (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 f)))))
     (mem2
     (tb2t2
     (apply (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 f)
     (t2tb3 x))) t)) :pattern ((mem
  (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb17 f)
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 s)
  (t2tb t)))
  (tb2t2
  (apply (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 int int)) (t2tb22 f)
     (infix_plmngt int int (t2tb1 s) (t2tb1 t))) (mem1 x
     (tb2t1 (dom int int (t2tb22 f))))) (mem1
     (tb2t3 (apply int int (t2tb22 f) (t2tb3 x))) t)) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb22 f)
  (infix_plmngt int int (t2tb1 s) (t2tb1 t)))
  (tb2t3 (apply int int (t2tb22 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x Int) (f uni) (s (set Int)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
     (mem1 x (tb2t1 (dom b int f)))) (mem b (apply b int f (t2tb3 x)) t)) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
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
  (forall ((a ty))
  (forall ((x uni) (z Int) (p uni) (q (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))
  (= (mem (tuple21 a int) (Tuple2 a int x (t2tb3 z))
  (semicolon int (tuple21 int enum_OBF__aa1) a p (t2tb q)))
  (exists ((y (tuple2 Int enum_OBF__aa)))
  (and (mem (tuple21 a (tuple21 int enum_OBF__aa1))
  (Tuple2 a (tuple21 int enum_OBF__aa1) x (t2tb6 y)) p) (mem2 (Tuple22 y z)
  q)))))))

;; semicolon_def
  (assert
  (forall ((a ty))
  (forall ((x uni) (z enum_OBF__aa) (p uni) (q (set (tuple2 Int
  enum_OBF__aa))))
  (= (mem (tuple21 a enum_OBF__aa1) (Tuple2 a enum_OBF__aa1 x (t2tb7 z))
  (semicolon enum_OBF__aa1 int a p (t2tb15 q)))
  (exists ((y Int))
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) p) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y z)) (t2tb15 q))))))))

;; semicolon_def
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Int enum_OBF__aa)) (z Int) (p uni) (q uni))
  (and
  (=> (mem2 (Tuple22 x z)
  (tb2t (semicolon int b (tuple21 int enum_OBF__aa1) p q)))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) b)
  (Tuple2 (tuple21 int enum_OBF__aa1) b (t2tb6 x) y) p) (mem (tuple21 b int)
  (Tuple2 b int y (t2tb3 z)) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) b)
  (Tuple2 (tuple21 int enum_OBF__aa1) b (t2tb6 x) y) p) (mem (tuple21 b int)
  (Tuple2 b int y (t2tb3 z)) q))) (mem2 (Tuple22 x z)
  (tb2t (semicolon int b (tuple21 int enum_OBF__aa1) p q))))))))

(declare-fun t2tb28 ((set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa))))) (sort
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)))
  (t2tb28 x))))

(declare-fun tb2t28 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa))))) (! (= (tb2t28 (t2tb28 i)) i) :pattern ((t2tb28 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb28 (tb2t28 j)) j) :pattern ((t2tb28 (tb2t28 j))) )))

(declare-fun t2tb29 ((tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int enum_OBF__aa))))
  (sort (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (t2tb29 x))))

(declare-fun tb2t29 (uni) (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int enum_OBF__aa))))
  (! (= (tb2t29 (t2tb29 i)) i) :pattern ((t2tb29 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb29 (tb2t29 j)) j) :pattern ((t2tb29 (tb2t29 j))) )))

;; semicolon_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (z Int) (p (set (tuple2 (tuple2 Int
  enum_OBF__aa) (tuple2 Int enum_OBF__aa)))) (q (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))
  (= (mem2 (Tuple22 x z)
  (tb2t
  (semicolon int (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)
  (t2tb28 p) (t2tb q))))
  (exists ((y (tuple2 Int enum_OBF__aa)))
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (t2tb6 y)) (t2tb28 p)) (mem2 (Tuple22 y z) q))))))

(declare-fun t2tb30 ((set (tuple2 (tuple2 Int enum_OBF__aa)
  enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa)))) (sort
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) enum_OBF__aa1)) (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa)
  enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb30 (tb2t30 j)) j) :pattern ((t2tb30 (tb2t30 j))) )))

(declare-fun t2tb31 ((tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa))) (sort
  (tuple21 (tuple21 int enum_OBF__aa1) enum_OBF__aa1) (t2tb31 x))))

(declare-fun tb2t31 (uni) (tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa)))
  (! (= (tb2t31 (t2tb31 i)) i) :pattern ((t2tb31 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb31 (tb2t31 j)) j) :pattern ((t2tb31 (tb2t31 j))) )))

;; semicolon_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (z enum_OBF__aa)
  (p (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (q (set (tuple2 Int
  enum_OBF__aa))))
  (= (mem (tuple21 (tuple21 int enum_OBF__aa1) enum_OBF__aa1)
  (Tuple2 (tuple21 int enum_OBF__aa1) enum_OBF__aa1 (t2tb6 x) (t2tb7 z))
  (semicolon enum_OBF__aa1 int (tuple21 int enum_OBF__aa1) (t2tb p)
  (t2tb15 q)))
  (exists ((y Int))
  (and (mem2 (Tuple22 x y) p) (mem (tuple21 int enum_OBF__aa1)
  (t2tb6 (Tuple21 y z)) (t2tb15 q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (z Int) (p (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (q (set (tuple2 Int Int))))
  (= (mem2 (Tuple22 x z)
  (tb2t (semicolon int int (tuple21 int enum_OBF__aa1) (t2tb p) (t2tb22 q))))
  (exists ((y Int))
  (and (mem2 (Tuple22 x y) p) (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 y) (t2tb3 z)) (t2tb22 q)))))))

;; semicolon_def
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 Int enum_OBF__aa)) (z uni) (p (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (q uni))
  (= (mem (tuple21 (tuple21 int enum_OBF__aa1) c)
  (Tuple2 (tuple21 int enum_OBF__aa1) c (t2tb6 x) z)
  (semicolon c int (tuple21 int enum_OBF__aa1) (t2tb p) q))
  (exists ((y Int))
  (and (mem2 (Tuple22 x y) p) (mem (tuple21 int c) (Tuple2 int c (t2tb3 y) z)
  q)))))))

;; semicolon_def
  (assert
  (forall ((b ty))
  (forall ((x Int) (z enum_OBF__aa) (p uni) (q uni))
  (and
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z))
  (semicolon enum_OBF__aa1 b int p q))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) p) (mem
  (tuple21 b enum_OBF__aa1) (Tuple2 b enum_OBF__aa1 y (t2tb7 z)) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) p) (mem
  (tuple21 b enum_OBF__aa1) (Tuple2 b enum_OBF__aa1 y (t2tb7 z)) q))) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z))
  (semicolon enum_OBF__aa1 b int p q)))))))

(declare-fun t2tb32 ((tuple2 enum_OBF__aa enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__aa enum_OBF__aa))) (sort
  (tuple21 enum_OBF__aa1 enum_OBF__aa1) (t2tb32 x))))

(declare-fun tb2t32 (uni) (tuple2 enum_OBF__aa enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__aa enum_OBF__aa)))
  (! (= (tb2t32 (t2tb32 i)) i) :pattern ((t2tb32 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 enum_OBF__aa1 enum_OBF__aa1) j)
     (= (t2tb32 (tb2t32 j)) j)) :pattern ((t2tb32 (tb2t32 j))) )))

(declare-fun t2tb33 ((set (tuple2 enum_OBF__aa enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__aa enum_OBF__aa)))) (sort
  (set1 (tuple21 enum_OBF__aa1 enum_OBF__aa1)) (t2tb33 x))))

(declare-fun tb2t33 (uni) (set (tuple2 enum_OBF__aa enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__aa enum_OBF__aa))))
  (! (= (tb2t33 (t2tb33 i)) i) :pattern ((t2tb33 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 enum_OBF__aa1 enum_OBF__aa1)) j)
     (= (t2tb33 (tb2t33 j)) j)) :pattern ((t2tb33 (tb2t33 j))) )))

;; semicolon_def
  (assert
  (forall ((x Int) (z enum_OBF__aa) (p (set (tuple2 Int enum_OBF__aa)))
  (q (set (tuple2 enum_OBF__aa enum_OBF__aa))))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z))
  (semicolon enum_OBF__aa1 enum_OBF__aa1 int (t2tb15 p) (t2tb33 q)))
  (exists ((y enum_OBF__aa))
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 p))
  (mem (tuple21 enum_OBF__aa1 enum_OBF__aa1)
  (Tuple2 enum_OBF__aa1 enum_OBF__aa1 (t2tb7 y) (t2tb7 z)) (t2tb33 q)))))))

;; semicolon_def
  (assert
  (forall ((c ty))
  (forall ((x Int) (z uni) (p (set (tuple2 Int enum_OBF__aa))) (q uni))
  (= (mem (tuple21 int c) (Tuple2 int c (t2tb3 x) z)
  (semicolon c enum_OBF__aa1 int (t2tb15 p) q))
  (exists ((y enum_OBF__aa))
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 p))
  (mem (tuple21 enum_OBF__aa1 c) (Tuple2 enum_OBF__aa1 c (t2tb7 y) z) q)))))))

;; semicolon_def
  (assert
  (forall ((x Int) (z enum_OBF__aa) (p (set (tuple2 Int Int)))
  (q (set (tuple2 Int enum_OBF__aa))))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z))
  (semicolon enum_OBF__aa1 int int (t2tb22 p) (t2tb15 q)))
  (exists ((y Int))
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
  (t2tb22 p)) (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y z))
  (t2tb15 q)))))))

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
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (! (and
     (=> (mem (tuple21 t (tuple21 (tuple21 int enum_OBF__aa1) int)) e
     (direct_product int (tuple21 int enum_OBF__aa1) t r1 r2))
     (exists ((x uni) (y (tuple2 Int enum_OBF__aa)) (z Int))
     (and (sort t x)
     (and
     (= (Tuple2 t (tuple21 (tuple21 int enum_OBF__aa1) int) x
        (t2tb2 (Tuple22 y z))) e)
     (and (mem (tuple21 t (tuple21 int enum_OBF__aa1))
     (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 y)) r1) (mem
     (tuple21 t int) (Tuple2 t int x (t2tb3 z)) r2))))))
     (=>
     (exists ((x uni) (y (tuple2 Int enum_OBF__aa)) (z Int))
     (and
     (= (Tuple2 t (tuple21 (tuple21 int enum_OBF__aa1) int) x
        (t2tb2 (Tuple22 y z))) e)
     (and (mem (tuple21 t (tuple21 int enum_OBF__aa1))
     (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 y)) r1) (mem
     (tuple21 t int) (Tuple2 t int x (t2tb3 z)) r2)))) (mem
     (tuple21 t (tuple21 (tuple21 int enum_OBF__aa1) int)) e
     (direct_product int (tuple21 int enum_OBF__aa1) t r1 r2)))) :pattern ((mem
  (tuple21 t (tuple21 (tuple21 int enum_OBF__aa1) int)) e
  (direct_product int (tuple21 int enum_OBF__aa1) t r1 r2))) ))))

;; direct_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (! (and
     (=> (mem (tuple21 t (tuple21 int enum_OBF__aa1)) e
     (direct_product enum_OBF__aa1 int t r1 r2))
     (exists ((x uni) (y Int) (z enum_OBF__aa))
     (and (sort t x)
     (and
     (= (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 (Tuple21 y z))) e)
     (and (mem (tuple21 t int) (Tuple2 t int x (t2tb3 y)) r1) (mem
     (tuple21 t enum_OBF__aa1) (Tuple2 t enum_OBF__aa1 x (t2tb7 z)) r2))))))
     (=>
     (exists ((x uni) (y Int) (z enum_OBF__aa))
     (and
     (= (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 (Tuple21 y z))) e)
     (and (mem (tuple21 t int) (Tuple2 t int x (t2tb3 y)) r1) (mem
     (tuple21 t enum_OBF__aa1) (Tuple2 t enum_OBF__aa1 x (t2tb7 z)) r2))))
     (mem (tuple21 t (tuple21 int enum_OBF__aa1)) e
     (direct_product enum_OBF__aa1 int t r1 r2)))) :pattern ((mem
  (tuple21 t (tuple21 int enum_OBF__aa1)) e
  (direct_product enum_OBF__aa1 int t r1 r2))) ))))

;; direct_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))
  (! (and
     (=> (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 u int)) e
     (direct_product int u (tuple21 int enum_OBF__aa1) r1 (t2tb r2)))
     (exists ((x (tuple2 Int enum_OBF__aa)) (y uni) (z Int))
     (and (sort u y)
     (and
     (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 u int) (t2tb6 x)
        (Tuple2 u int y (t2tb3 z))) e)
     (and (mem (tuple21 (tuple21 int enum_OBF__aa1) u)
     (Tuple2 (tuple21 int enum_OBF__aa1) u (t2tb6 x) y) r1) (mem2
     (Tuple22 x z) r2))))))
     (=>
     (exists ((x (tuple2 Int enum_OBF__aa)) (y uni) (z Int))
     (and
     (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 u int) (t2tb6 x)
        (Tuple2 u int y (t2tb3 z))) e)
     (and (mem (tuple21 (tuple21 int enum_OBF__aa1) u)
     (Tuple2 (tuple21 int enum_OBF__aa1) u (t2tb6 x) y) r1) (mem2
     (Tuple22 x z) r2)))) (mem
     (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 u int)) e
     (direct_product int u (tuple21 int enum_OBF__aa1) r1 (t2tb r2))))) :pattern ((mem
  (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 u int)) e
  (direct_product int u (tuple21 int enum_OBF__aa1) r1 (t2tb r2)))) ))))

(declare-fun t2tb34 ((set (tuple2 (tuple2 Int enum_OBF__aa)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))) (sort
  (set1
  (tuple21 (tuple21 int enum_OBF__aa1)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb34 x))))

(declare-fun tb2t34 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))
  (! (= (tb2t34 (t2tb34 i)) i) :pattern ((t2tb34 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb34 (tb2t34 j)) j) :pattern ((t2tb34 (tb2t34 j))) )))

(declare-fun t2tb35 ((tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) (sort
  (tuple21 (tuple21 int enum_OBF__aa1)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb35 x))))

(declare-fun tb2t35 (uni) (tuple2 (tuple2 Int enum_OBF__aa)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) (! (= (tb2t35 (t2tb35 i)) i) :pattern ((t2tb35 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb35 (tb2t35 j)) j) :pattern ((t2tb35 (tb2t35 j))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)))) (r2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (mem
     (tuple21 (tuple21 int enum_OBF__aa1)
     (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb35 e)
     (direct_product int (tuple21 int enum_OBF__aa1)
     (tuple21 int enum_OBF__aa1) (t2tb28 r1) (t2tb r2)))
     (exists ((x (tuple2 Int enum_OBF__aa)) (y (tuple2 Int enum_OBF__aa))
     (z Int))
     (and
     (= (tb2t35
        (Tuple2 (tuple21 int enum_OBF__aa1)
        (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb6 x)
        (t2tb2 (Tuple22 y z)))) e)
     (and (mem
     (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
     (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)
     (t2tb6 x) (t2tb6 y)) (t2tb28 r1)) (mem2 (Tuple22 x z) r2))))) :pattern ((mem
  (tuple21 (tuple21 int enum_OBF__aa1)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb35 e)
  (direct_product int (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)
  (t2tb28 r1) (t2tb r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int enum_OBF__aa)))
  (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 (set (tuple2 (tuple2 Int enum_OBF__aa) enum_OBF__aa))))
  (! (= (mem
     (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
     (t2tb29 e)
     (direct_product enum_OBF__aa1 int (tuple21 int enum_OBF__aa1) (t2tb r1)
     (t2tb30 r2)))
     (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z enum_OBF__aa))
     (and
     (= (tb2t29
        (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)
        (t2tb6 x) (t2tb6 (Tuple21 y z)))) e)
     (and (mem2 (Tuple22 x y) r1) (mem
     (tuple21 (tuple21 int enum_OBF__aa1) enum_OBF__aa1)
     (Tuple2 (tuple21 int enum_OBF__aa1) enum_OBF__aa1 (t2tb6 x) (t2tb7 z))
     (t2tb30 r2)))))) :pattern ((mem
  (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (t2tb29 e)
  (direct_product enum_OBF__aa1 int (tuple21 int enum_OBF__aa1) (t2tb r1)
  (t2tb30 r2)))) )))

(declare-fun t2tb36 ((set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int Int)))))
  (sort (set1 (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int int)))
  (t2tb36 x))))

(declare-fun tb2t36 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int Int)))))
  (! (= (tb2t36 (t2tb36 i)) i) :pattern ((t2tb36 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb36 (tb2t36 j)) j) :pattern ((t2tb36 (tb2t36 j))) )))

(declare-fun t2tb37 ((tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int Int)))) (sort
  (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int int)) (t2tb37 x))))

(declare-fun tb2t37 (uni) (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int Int))))
  (! (= (tb2t37 (t2tb37 i)) i) :pattern ((t2tb37 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb37 (tb2t37 j)) j) :pattern ((t2tb37 (tb2t37 j))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int Int)))
  (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int int))
     (t2tb37 e)
     (direct_product int int (tuple21 int enum_OBF__aa1) (t2tb r1) (t2tb r2)))
     (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z Int))
     (and
     (= (tb2t37
        (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int int) (t2tb6 x)
        (Tuple2 int int (t2tb3 y) (t2tb3 z)))) e)
     (and (mem2 (Tuple22 x y) r1) (mem2 (Tuple22 x z) r2))))) :pattern ((mem
  (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int int)) (t2tb37 e)
  (direct_product int int (tuple21 int enum_OBF__aa1) (t2tb r1) (t2tb r2)))) )))

;; direct_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 uni))
  (! (and
     (=> (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int v)) e
     (direct_product v int (tuple21 int enum_OBF__aa1) (t2tb r1) r2))
     (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z uni))
     (and (sort v z)
     (and
     (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int v) (t2tb6 x)
        (Tuple2 int v (t2tb3 y) z)) e)
     (and (mem2 (Tuple22 x y) r1) (mem
     (tuple21 (tuple21 int enum_OBF__aa1) v)
     (Tuple2 (tuple21 int enum_OBF__aa1) v (t2tb6 x) z) r2))))))
     (=>
     (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z uni))
     (and
     (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int v) (t2tb6 x)
        (Tuple2 int v (t2tb3 y) z)) e)
     (and (mem2 (Tuple22 x y) r1) (mem
     (tuple21 (tuple21 int enum_OBF__aa1) v)
     (Tuple2 (tuple21 int enum_OBF__aa1) v (t2tb6 x) z) r2)))) (mem
     (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int v)) e
     (direct_product v int (tuple21 int enum_OBF__aa1) (t2tb r1) r2)))) :pattern ((mem
  (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int v)) e
  (direct_product v int (tuple21 int enum_OBF__aa1) (t2tb r1) r2))) ))))

;; direct_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Int enum_OBF__aa))))
  (! (and
     (=> (mem (tuple21 int (tuple21 u enum_OBF__aa1)) e
     (direct_product enum_OBF__aa1 u int r1 (t2tb15 r2)))
     (exists ((x Int) (y uni) (z enum_OBF__aa))
     (and (sort u y)
     (and
     (= (Tuple2 int (tuple21 u enum_OBF__aa1) (t2tb3 x)
        (Tuple2 u enum_OBF__aa1 y (t2tb7 z))) e)
     (and (mem (tuple21 int u) (Tuple2 int u (t2tb3 x) y) r1) (mem
     (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r2)))))))
     (=>
     (exists ((x Int) (y uni) (z enum_OBF__aa))
     (and
     (= (Tuple2 int (tuple21 u enum_OBF__aa1) (t2tb3 x)
        (Tuple2 u enum_OBF__aa1 y (t2tb7 z))) e)
     (and (mem (tuple21 int u) (Tuple2 int u (t2tb3 x) y) r1) (mem
     (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r2))))) (mem
     (tuple21 int (tuple21 u enum_OBF__aa1)) e
     (direct_product enum_OBF__aa1 u int r1 (t2tb15 r2))))) :pattern ((mem
  (tuple21 int (tuple21 u enum_OBF__aa1)) e
  (direct_product enum_OBF__aa1 u int r1 (t2tb15 r2)))) ))))

(declare-fun t2tb38 ((set (tuple2 Int (tuple2 enum_OBF__aa
  enum_OBF__aa)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa))))) (sort
  (set1 (tuple21 int (tuple21 enum_OBF__aa1 enum_OBF__aa1))) (t2tb38 x))))

(declare-fun tb2t38 (uni) (set (tuple2 Int (tuple2 enum_OBF__aa
  enum_OBF__aa))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa)))))
  (! (= (tb2t38 (t2tb38 i)) i) :pattern ((t2tb38 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb38 (tb2t38 j)) j) :pattern ((t2tb38 (tb2t38 j))) )))

(declare-fun t2tb39 ((tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa)))) (sort
  (tuple21 int (tuple21 enum_OBF__aa1 enum_OBF__aa1)) (t2tb39 x))))

(declare-fun tb2t39 (uni) (tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa))))
  (! (= (tb2t39 (t2tb39 i)) i) :pattern ((t2tb39 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb39 (tb2t39 j)) j) :pattern ((t2tb39 (tb2t39 j))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 Int (tuple2 enum_OBF__aa enum_OBF__aa)))
  (r1 (set (tuple2 Int enum_OBF__aa))) (r2 (set (tuple2 Int enum_OBF__aa))))
  (! (= (mem (tuple21 int (tuple21 enum_OBF__aa1 enum_OBF__aa1)) (t2tb39 e)
     (direct_product enum_OBF__aa1 enum_OBF__aa1 int (t2tb15 r1) (t2tb15 r2)))
     (exists ((x Int) (y enum_OBF__aa) (z enum_OBF__aa))
     (and
     (= (tb2t39
        (Tuple2 int (tuple21 enum_OBF__aa1 enum_OBF__aa1) (t2tb3 x)
        (Tuple2 enum_OBF__aa1 enum_OBF__aa1 (t2tb7 y) (t2tb7 z)))) e)
     (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r1))
     (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r2)))))) :pattern ((mem
  (tuple21 int (tuple21 enum_OBF__aa1 enum_OBF__aa1)) (t2tb39 e)
  (direct_product enum_OBF__aa1 enum_OBF__aa1 int (t2tb15 r1) (t2tb15 r2)))) )))

;; direct_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 Int enum_OBF__aa))) (r2 uni))
  (! (and
     (=> (mem (tuple21 int (tuple21 enum_OBF__aa1 v)) e
     (direct_product v enum_OBF__aa1 int (t2tb15 r1) r2))
     (exists ((x Int) (y enum_OBF__aa) (z uni))
     (and (sort v z)
     (and
     (= (Tuple2 int (tuple21 enum_OBF__aa1 v) (t2tb3 x)
        (Tuple2 enum_OBF__aa1 v (t2tb7 y) z)) e)
     (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r1))
     (mem (tuple21 int v) (Tuple2 int v (t2tb3 x) z) r2))))))
     (=>
     (exists ((x Int) (y enum_OBF__aa) (z uni))
     (and
     (= (Tuple2 int (tuple21 enum_OBF__aa1 v) (t2tb3 x)
        (Tuple2 enum_OBF__aa1 v (t2tb7 y) z)) e)
     (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r1))
     (mem (tuple21 int v) (Tuple2 int v (t2tb3 x) z) r2)))) (mem
     (tuple21 int (tuple21 enum_OBF__aa1 v)) e
     (direct_product v enum_OBF__aa1 int (t2tb15 r1) r2)))) :pattern ((mem
  (tuple21 int (tuple21 enum_OBF__aa1 v)) e
  (direct_product v enum_OBF__aa1 int (t2tb15 r1) r2))) ))))

;; direct_product_def
  (assert
  (forall ((e (tuple2 Int (tuple2 Int enum_OBF__aa))) (r1 (set (tuple2 Int
  Int))) (r2 (set (tuple2 Int enum_OBF__aa))))
  (! (= (mem (tuple21 int (tuple21 int enum_OBF__aa1)) (t2tb25 e)
     (direct_product enum_OBF__aa1 int int (t2tb22 r1) (t2tb15 r2)))
     (exists ((x Int) (y Int) (z enum_OBF__aa))
     (and
     (= (tb2t25
        (Tuple2 int (tuple21 int enum_OBF__aa1) (t2tb3 x)
        (t2tb6 (Tuple21 y z)))) e)
     (and (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
     (t2tb22 r1)) (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z))
     (t2tb15 r2)))))) :pattern ((mem
  (tuple21 int (tuple21 int enum_OBF__aa1)) (t2tb25 e)
  (direct_product enum_OBF__aa1 int int (t2tb22 r1) (t2tb15 r2)))) )))

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
  (forall ((t ty) (u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))
  (and
  (=> (mem (tuple21 (tuple21 t (tuple21 int enum_OBF__aa1)) (tuple21 u int))
  e (parallel_product int (tuple21 int enum_OBF__aa1) u t r1 (t2tb r2)))
  (exists ((x uni) (y (tuple2 Int enum_OBF__aa)) (z uni) (a Int))
  (and (sort t x)
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 t (tuple21 int enum_OBF__aa1)) (tuple21 u int)
     (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 y))
     (Tuple2 u int z (t2tb3 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem2 (Tuple22 y a) r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 Int enum_OBF__aa)) (z uni) (a Int))
  (and
  (= (Tuple2 (tuple21 t (tuple21 int enum_OBF__aa1)) (tuple21 u int)
     (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 y))
     (Tuple2 u int z (t2tb3 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem2 (Tuple22 y a) r2))))
  (mem (tuple21 (tuple21 t (tuple21 int enum_OBF__aa1)) (tuple21 u int)) e
  (parallel_product int (tuple21 int enum_OBF__aa1) u t r1 (t2tb r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Int enum_OBF__aa))))
  (and
  (=> (mem (tuple21 (tuple21 t int) (tuple21 u enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 int u t r1 (t2tb15 r2)))
  (exists ((x uni) (y Int) (z uni) (a enum_OBF__aa))
  (and (sort t x)
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 t int) (tuple21 u enum_OBF__aa1)
     (Tuple2 t int x (t2tb3 y)) (Tuple2 u enum_OBF__aa1 z (t2tb7 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2))))))))
  (=>
  (exists ((x uni) (y Int) (z uni) (a enum_OBF__aa))
  (and
  (= (Tuple2 (tuple21 t int) (tuple21 u enum_OBF__aa1)
     (Tuple2 t int x (t2tb3 y)) (Tuple2 u enum_OBF__aa1 z (t2tb7 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2))))) (mem
  (tuple21 (tuple21 t int) (tuple21 u enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 int u t r1 (t2tb15 r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 t v) (tuple21 (tuple21 int enum_OBF__aa1) int))
  e (parallel_product int v (tuple21 int enum_OBF__aa1) t r1 r2))
  (exists ((x uni) (y uni) (z (tuple2 Int enum_OBF__aa)) (a Int))
  (and (sort t x)
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 (tuple21 int enum_OBF__aa1) int)
     (Tuple2 t v x y) (t2tb2 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 int enum_OBF__aa1))
  (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 z)) r1) (mem (tuple21 v int)
  (Tuple2 v int y (t2tb3 a)) r2)))))))
  (=>
  (exists ((x uni) (y uni) (z (tuple2 Int enum_OBF__aa)) (a Int))
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 (tuple21 int enum_OBF__aa1) int)
     (Tuple2 t v x y) (t2tb2 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 int enum_OBF__aa1))
  (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 z)) r1) (mem (tuple21 v int)
  (Tuple2 v int y (t2tb3 a)) r2)))) (mem
  (tuple21 (tuple21 t v) (tuple21 (tuple21 int enum_OBF__aa1) int)) e
  (parallel_product int v (tuple21 int enum_OBF__aa1) t r1 r2)))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 int enum_OBF__aa1))
  (tuple21 (tuple21 int enum_OBF__aa1) int)) e
  (parallel_product int (tuple21 int enum_OBF__aa1)
  (tuple21 int enum_OBF__aa1) t r1 (t2tb r2)))
  (exists ((x uni) (y (tuple2 Int enum_OBF__aa)) (z (tuple2 Int
  enum_OBF__aa)) (a Int))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 int enum_OBF__aa1))
     (tuple21 (tuple21 int enum_OBF__aa1) int)
     (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 y))
     (t2tb2 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 int enum_OBF__aa1))
  (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 z)) r1) (mem2 (Tuple22 y a)
  r2))))))
  (=>
  (exists ((x uni) (y (tuple2 Int enum_OBF__aa)) (z (tuple2 Int
  enum_OBF__aa)) (a Int))
  (and
  (= (Tuple2 (tuple21 t (tuple21 int enum_OBF__aa1))
     (tuple21 (tuple21 int enum_OBF__aa1) int)
     (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 y))
     (t2tb2 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 int enum_OBF__aa1))
  (Tuple2 t (tuple21 int enum_OBF__aa1) x (t2tb6 z)) r1) (mem2 (Tuple22 y a)
  r2)))) (mem
  (tuple21 (tuple21 t (tuple21 int enum_OBF__aa1))
  (tuple21 (tuple21 int enum_OBF__aa1) int)) e
  (parallel_product int (tuple21 int enum_OBF__aa1)
  (tuple21 int enum_OBF__aa1) t r1 (t2tb r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 t v) (tuple21 int enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 v int t r1 r2))
  (exists ((x uni) (y uni) (z Int) (a enum_OBF__aa))
  (and (sort t x)
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 int enum_OBF__aa1) (Tuple2 t v x y)
     (t2tb6 (Tuple21 z a))) e)
  (and (mem (tuple21 t int) (Tuple2 t int x (t2tb3 z)) r1) (mem
  (tuple21 v enum_OBF__aa1) (Tuple2 v enum_OBF__aa1 y (t2tb7 a)) r2)))))))
  (=>
  (exists ((x uni) (y uni) (z Int) (a enum_OBF__aa))
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 int enum_OBF__aa1) (Tuple2 t v x y)
     (t2tb6 (Tuple21 z a))) e)
  (and (mem (tuple21 t int) (Tuple2 t int x (t2tb3 z)) r1) (mem
  (tuple21 v enum_OBF__aa1) (Tuple2 v enum_OBF__aa1 y (t2tb7 a)) r2)))) (mem
  (tuple21 (tuple21 t v) (tuple21 int enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 v int t r1 r2)))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Int enum_OBF__aa))))
  (and
  (=> (mem (tuple21 (tuple21 t int) (tuple21 int enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 int int t r1 (t2tb15 r2)))
  (exists ((x uni) (y Int) (z Int) (a enum_OBF__aa))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t int) (tuple21 int enum_OBF__aa1)
     (Tuple2 t int x (t2tb3 y)) (t2tb6 (Tuple21 z a))) e)
  (and (mem (tuple21 t int) (Tuple2 t int x (t2tb3 z)) r1) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2)))))))
  (=>
  (exists ((x uni) (y Int) (z Int) (a enum_OBF__aa))
  (and
  (= (Tuple2 (tuple21 t int) (tuple21 int enum_OBF__aa1)
     (Tuple2 t int x (t2tb3 y)) (t2tb6 (Tuple21 z a))) e)
  (and (mem (tuple21 t int) (Tuple2 t int x (t2tb3 z)) r1) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2))))) (mem
  (tuple21 (tuple21 t int) (tuple21 int enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 int int t r1 (t2tb15 r2))))))))

;; parallel_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Int enum_OBF__aa))))
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 u enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 int u (tuple21 int enum_OBF__aa1) r1
  (t2tb15 r2)))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z uni) (a enum_OBF__aa))
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 u enum_OBF__aa1) (t2tb2 (Tuple22 x y))
     (Tuple2 u enum_OBF__aa1 z (t2tb7 a))) e)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) u)
  (Tuple2 (tuple21 int enum_OBF__aa1) u (t2tb6 x) z) r1) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2)))))))
  (=>
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z uni) (a enum_OBF__aa))
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 u enum_OBF__aa1) (t2tb2 (Tuple22 x y))
     (Tuple2 u enum_OBF__aa1 z (t2tb7 a))) e)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) u)
  (Tuple2 (tuple21 int enum_OBF__aa1) u (t2tb6 x) z) r1) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2))))) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 u enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 int u (tuple21 int enum_OBF__aa1) r1
  (t2tb15 r2))))))))

;; parallel_product_def
  (assert
  (forall ((u ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 u w))
  e (parallel_product w int u (tuple21 int enum_OBF__aa1) r1 r2))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z uni) (a uni))
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 u w)
     (t2tb2 (Tuple22 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) u)
  (Tuple2 (tuple21 int enum_OBF__aa1) u (t2tb6 x) z) r1) (mem (tuple21 int w)
  (Tuple2 int w (t2tb3 y) a) r2)))))))
  (=>
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 u w)
     (t2tb2 (Tuple22 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) u)
  (Tuple2 (tuple21 int enum_OBF__aa1) u (t2tb6 x) z) r1) (mem (tuple21 int w)
  (Tuple2 int w (t2tb3 y) a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 u w)) e
  (parallel_product w int u (tuple21 int enum_OBF__aa1) r1 r2)))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))) (r1 (set (tuple2 (tuple2 Int
  enum_OBF__aa) (tuple2 Int enum_OBF__aa)))) (r2 (set (tuple2 Int Int))))
  (= (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb10 e)
  (parallel_product int int (tuple21 int enum_OBF__aa1)
  (tuple21 int enum_OBF__aa1) (t2tb28 r1) (t2tb22 r2)))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z (tuple2 Int
  enum_OBF__aa)) (a Int))
  (and
  (= (tb2t10
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
     (t2tb2 (Tuple22 z a)))) e)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (t2tb6 z)) (t2tb28 r1)) (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 y) (t2tb3 a)) (t2tb22 r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 uni))
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) v)
  (tuple21 int enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 v int (tuple21 int enum_OBF__aa1) (t2tb r1)
  r2))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y uni) (z Int) (a enum_OBF__aa))
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) v)
     (tuple21 int enum_OBF__aa1)
     (Tuple2 (tuple21 int enum_OBF__aa1) v (t2tb6 x) y)
     (t2tb6 (Tuple21 z a))) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 v enum_OBF__aa1)
  (Tuple2 v enum_OBF__aa1 y (t2tb7 a)) r2))))))
  (=>
  (exists ((x (tuple2 Int enum_OBF__aa)) (y uni) (z Int) (a enum_OBF__aa))
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) v)
     (tuple21 int enum_OBF__aa1)
     (Tuple2 (tuple21 int enum_OBF__aa1) v (t2tb6 x) y)
     (t2tb6 (Tuple21 z a))) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 v enum_OBF__aa1)
  (Tuple2 v enum_OBF__aa1 y (t2tb7 a)) r2)))) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) v)
  (tuple21 int enum_OBF__aa1)) e
  (parallel_product enum_OBF__aa1 v int (tuple21 int enum_OBF__aa1) (t2tb r1)
  r2)))))))

(declare-fun t2tb40 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  (tuple2 Int enum_OBF__aa)) (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)) (tuple2 Int Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (tuple21 int int))) (t2tb40 x))))

(declare-fun tb2t40 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  (tuple2 Int enum_OBF__aa)) (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)) (tuple2 Int Int)))))
  (! (= (tb2t40 (t2tb40 i)) i) :pattern ((t2tb40 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb40 (tb2t40 j)) j) :pattern ((t2tb40 (tb2t40 j))) )))

(declare-fun t2tb41 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)) (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)) (tuple2 Int Int)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (tuple21 int int)) (t2tb41 x))))

(declare-fun tb2t41 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  (tuple2 Int enum_OBF__aa)) (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)) (tuple2 Int Int))))
  (! (= (tb2t41 (t2tb41 i)) i) :pattern ((t2tb41 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb41 (tb2t41 j)) j) :pattern ((t2tb41 (tb2t41 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int
  enum_OBF__aa)) (tuple2 Int Int))) (r1 (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (r2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (tuple21 int int)) (t2tb41 e)
  (parallel_product int (tuple21 int enum_OBF__aa1) int
  (tuple21 int enum_OBF__aa1) (t2tb r1) (t2tb r2)))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y (tuple2 Int enum_OBF__aa))
  (z Int) (a Int))
  (and
  (= (tb2t41
     (Tuple2
     (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
     (tuple21 int int)
     (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)
     (t2tb6 x) (t2tb6 y)) (Tuple2 int int (t2tb3 z) (t2tb3 a)))) e)
  (and (mem2 (Tuple22 x z) r1) (mem2 (Tuple22 y a) r2)))))))

(declare-fun t2tb42 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int enum_OBF__aa)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  enum_OBF__aa))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 int enum_OBF__aa1))) (t2tb42 x))))

(declare-fun tb2t42 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int enum_OBF__aa))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  enum_OBF__aa))))) (! (= (tb2t42 (t2tb42 i)) i) :pattern ((t2tb42 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb42 (tb2t42 j)) j) :pattern ((t2tb42 (tb2t42 j))) )))

(declare-fun t2tb43 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  enum_OBF__aa)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 int enum_OBF__aa1)) (t2tb43 x))))

(declare-fun tb2t43 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  enum_OBF__aa)))) (! (= (tb2t43 (t2tb43 i)) i) :pattern ((t2tb43 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb43 (tb2t43 j)) j) :pattern ((t2tb43 (tb2t43 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  enum_OBF__aa))) (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 (set (tuple2 Int enum_OBF__aa))))
  (= (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 int enum_OBF__aa1)) (t2tb43 e)
  (parallel_product enum_OBF__aa1 int int (tuple21 int enum_OBF__aa1)
  (t2tb r1) (t2tb15 r2)))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z Int) (a enum_OBF__aa))
  (and
  (= (tb2t43
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 int enum_OBF__aa1) (t2tb2 (Tuple22 x y)) (t2tb6 (Tuple21 z a)))) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 int enum_OBF__aa1)
  (t2tb6 (Tuple21 y a)) (t2tb15 r2))))))))

;; parallel_product_def
  (assert
  (forall ((w ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 uni))
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int w)) e
  (parallel_product w int int (tuple21 int enum_OBF__aa1) (t2tb r1) r2))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z Int) (a uni))
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int w)
     (t2tb2 (Tuple22 x y)) (Tuple2 int w (t2tb3 z) a)) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 int w)
  (Tuple2 int w (t2tb3 y) a) r2))))))
  (=>
  (exists ((x (tuple2 Int enum_OBF__aa)) (y Int) (z Int) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int w)
     (t2tb2 (Tuple22 x y)) (Tuple2 int w (t2tb3 z) a)) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 int w)
  (Tuple2 int w (t2tb3 y) a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int w)) e
  (parallel_product w int int (tuple21 int enum_OBF__aa1) (t2tb r1) r2)))))))

;; parallel_product_def
  (assert
  (forall ((v ty) (w ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) v) (tuple21 int w))
  e (parallel_product w v int (tuple21 int enum_OBF__aa1) (t2tb r1) r2))
  (exists ((x (tuple2 Int enum_OBF__aa)) (y uni) (z Int) (a uni))
  (and (sort v y)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) v) (tuple21 int w)
     (Tuple2 (tuple21 int enum_OBF__aa1) v (t2tb6 x) y)
     (Tuple2 int w (t2tb3 z) a)) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 v w) (Tuple2 v w y a) r2)))))))
  (=>
  (exists ((x (tuple2 Int enum_OBF__aa)) (y uni) (z Int) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) v) (tuple21 int w)
     (Tuple2 (tuple21 int enum_OBF__aa1) v (t2tb6 x) y)
     (Tuple2 int w (t2tb3 z) a)) e)
  (and (mem2 (Tuple22 x z) r1) (mem (tuple21 v w) (Tuple2 v w y a) r2))))
  (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) v) (tuple21 int w)) e
  (parallel_product w v int (tuple21 int enum_OBF__aa1) (t2tb r1) r2)))))))

;; parallel_product_def
  (assert
  (forall ((u ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 u w)) e
  (parallel_product w enum_OBF__aa1 u int r1 r2))
  (exists ((x Int) (y enum_OBF__aa) (z uni) (a uni))
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 u w) (t2tb6 (Tuple21 x y))
     (Tuple2 u w z a)) e)
  (and (mem (tuple21 int u) (Tuple2 int u (t2tb3 x) z) r1) (mem
  (tuple21 enum_OBF__aa1 w) (Tuple2 enum_OBF__aa1 w (t2tb7 y) a) r2)))))))
  (=>
  (exists ((x Int) (y enum_OBF__aa) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 u w) (t2tb6 (Tuple21 x y))
     (Tuple2 u w z a)) e)
  (and (mem (tuple21 int u) (Tuple2 int u (t2tb3 x) z) r1) (mem
  (tuple21 enum_OBF__aa1 w) (Tuple2 enum_OBF__aa1 w (t2tb7 y) a) r2)))) (mem
  (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 u w)) e
  (parallel_product w enum_OBF__aa1 u int r1 r2)))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (r1 (set (tuple2 Int (tuple2 Int enum_OBF__aa))))
  (r2 (set (tuple2 enum_OBF__aa Int))))
  (= (mem
  (tuple21 (tuple21 int enum_OBF__aa1)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb35 e)
  (parallel_product int enum_OBF__aa1 (tuple21 int enum_OBF__aa1) int
  (t2tb24 r1) (t2tb26 r2)))
  (exists ((x Int) (y enum_OBF__aa) (z (tuple2 Int enum_OBF__aa)) (a Int))
  (and
  (= (tb2t35
     (Tuple2 (tuple21 int enum_OBF__aa1)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb6 (Tuple21 x y))
     (t2tb2 (Tuple22 z a)))) e)
  (and (mem (tuple21 int (tuple21 int enum_OBF__aa1))
  (Tuple2 int (tuple21 int enum_OBF__aa1) (t2tb3 x) (t2tb6 z)) (t2tb24 r1))
  (mem (tuple21 enum_OBF__aa1 int)
  (Tuple2 enum_OBF__aa1 int (t2tb7 y) (t2tb3 a)) (t2tb26 r2))))))))

(declare-fun t2tb44 ((set (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int))))) (sort
  (set1
  (tuple21 (tuple21 int (tuple21 int enum_OBF__aa1))
  (tuple21 enum_OBF__aa1 int))) (t2tb44 x))))

(declare-fun tb2t44 (uni) (set (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int)))))
  (! (= (tb2t44 (t2tb44 i)) i) :pattern ((t2tb44 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb44 (tb2t44 j)) j) :pattern ((t2tb44 (tb2t44 j))) )))

(declare-fun t2tb45 ((tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int)))) (sort
  (tuple21 (tuple21 int (tuple21 int enum_OBF__aa1))
  (tuple21 enum_OBF__aa1 int)) (t2tb45 x))))

(declare-fun tb2t45 (uni) (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int))))
  (! (= (tb2t45 (t2tb45 i)) i) :pattern ((t2tb45 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb45 (tb2t45 j)) j) :pattern ((t2tb45 (tb2t45 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int (tuple2 Int enum_OBF__aa))
  (tuple2 enum_OBF__aa Int))) (r1 (set (tuple2 Int enum_OBF__aa)))
  (r2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem
  (tuple21 (tuple21 int (tuple21 int enum_OBF__aa1))
  (tuple21 enum_OBF__aa1 int)) (t2tb45 e)
  (parallel_product int (tuple21 int enum_OBF__aa1) enum_OBF__aa1 int
  (t2tb15 r1) (t2tb r2)))
  (exists ((x Int) (y (tuple2 Int enum_OBF__aa)) (z enum_OBF__aa) (a Int))
  (and
  (= (tb2t45
     (Tuple2 (tuple21 int (tuple21 int enum_OBF__aa1))
     (tuple21 enum_OBF__aa1 int)
     (Tuple2 int (tuple21 int enum_OBF__aa1) (t2tb3 x) (t2tb6 y))
     (Tuple2 enum_OBF__aa1 int (t2tb7 z) (t2tb3 a)))) e)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r1))
  (mem2 (Tuple22 y a) r2)))))))

;; parallel_product_def
  (assert
  (forall ((w ty))
  (forall ((e uni) (r1 (set (tuple2 Int enum_OBF__aa))) (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 enum_OBF__aa1 w)) e
  (parallel_product w enum_OBF__aa1 enum_OBF__aa1 int (t2tb15 r1) r2))
  (exists ((x Int) (y enum_OBF__aa) (z enum_OBF__aa) (a uni))
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 enum_OBF__aa1 w)
     (t2tb6 (Tuple21 x y)) (Tuple2 enum_OBF__aa1 w (t2tb7 z) a)) e)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r1))
  (mem (tuple21 enum_OBF__aa1 w) (Tuple2 enum_OBF__aa1 w (t2tb7 y) a) r2))))))
  (=>
  (exists ((x Int) (y enum_OBF__aa) (z enum_OBF__aa) (a uni))
  (and
  (= (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 enum_OBF__aa1 w)
     (t2tb6 (Tuple21 x y)) (Tuple2 enum_OBF__aa1 w (t2tb7 z) a)) e)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r1))
  (mem (tuple21 enum_OBF__aa1 w) (Tuple2 enum_OBF__aa1 w (t2tb7 y) a) r2))))
  (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 enum_OBF__aa1 w)) e
  (parallel_product w enum_OBF__aa1 enum_OBF__aa1 int (t2tb15 r1) r2)))))))

(declare-fun t2tb46 ((set (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa
  enum_OBF__aa)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa
  enum_OBF__aa))))) (sort
  (set1 (tuple21 (tuple21 int int) (tuple21 enum_OBF__aa1 enum_OBF__aa1)))
  (t2tb46 x))))

(declare-fun tb2t46 (uni) (set (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa
  enum_OBF__aa))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa
  enum_OBF__aa))))) (! (= (tb2t46 (t2tb46 i)) i) :pattern ((t2tb46 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb46 (tb2t46 j)) j) :pattern ((t2tb46 (tb2t46 j))) )))

(declare-fun t2tb47 ((tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa
  enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa enum_OBF__aa))))
  (sort (tuple21 (tuple21 int int) (tuple21 enum_OBF__aa1 enum_OBF__aa1))
  (t2tb47 x))))

(declare-fun tb2t47 (uni) (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa
  enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa enum_OBF__aa))))
  (! (= (tb2t47 (t2tb47 i)) i) :pattern ((t2tb47 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb47 (tb2t47 j)) j) :pattern ((t2tb47 (tb2t47 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int Int) (tuple2 enum_OBF__aa enum_OBF__aa)))
  (r1 (set (tuple2 Int enum_OBF__aa))) (r2 (set (tuple2 Int enum_OBF__aa))))
  (= (mem (tuple21 (tuple21 int int) (tuple21 enum_OBF__aa1 enum_OBF__aa1))
  (t2tb47 e)
  (parallel_product enum_OBF__aa1 int enum_OBF__aa1 int (t2tb15 r1)
  (t2tb15 r2)))
  (exists ((x Int) (y Int) (z enum_OBF__aa) (a enum_OBF__aa))
  (and
  (= (tb2t47
     (Tuple2 (tuple21 int int) (tuple21 enum_OBF__aa1 enum_OBF__aa1)
     (Tuple2 int int (t2tb3 x) (t2tb3 y))
     (Tuple2 enum_OBF__aa1 enum_OBF__aa1 (t2tb7 z) (t2tb7 a)))) e)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r1))
  (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 y a)) (t2tb15 r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty) (w ty))
  (forall ((e uni) (r1 (set (tuple2 Int enum_OBF__aa))) (r2 uni))
  (and
  (=> (mem (tuple21 (tuple21 int v) (tuple21 enum_OBF__aa1 w)) e
  (parallel_product w v enum_OBF__aa1 int (t2tb15 r1) r2))
  (exists ((x Int) (y uni) (z enum_OBF__aa) (a uni))
  (and (sort v y)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 int v) (tuple21 enum_OBF__aa1 w)
     (Tuple2 int v (t2tb3 x) y) (Tuple2 enum_OBF__aa1 w (t2tb7 z) a)) e)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r1))
  (mem (tuple21 v w) (Tuple2 v w y a) r2)))))))
  (=>
  (exists ((x Int) (y uni) (z enum_OBF__aa) (a uni))
  (and
  (= (Tuple2 (tuple21 int v) (tuple21 enum_OBF__aa1 w)
     (Tuple2 int v (t2tb3 x) y) (Tuple2 enum_OBF__aa1 w (t2tb7 z) a)) e)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x z)) (t2tb15 r1))
  (mem (tuple21 v w) (Tuple2 v w y a) r2)))) (mem
  (tuple21 (tuple21 int v) (tuple21 enum_OBF__aa1 w)) e
  (parallel_product w v enum_OBF__aa1 int (t2tb15 r1) r2)))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Int enum_OBF__aa) (tuple2 Int enum_OBF__aa)))
  (r1 (set (tuple2 Int Int))) (r2 (set (tuple2 enum_OBF__aa enum_OBF__aa))))
  (= (mem (tuple21 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1))
  (t2tb29 e)
  (parallel_product enum_OBF__aa1 enum_OBF__aa1 int int (t2tb22 r1)
  (t2tb33 r2)))
  (exists ((x Int) (y enum_OBF__aa) (z Int) (a enum_OBF__aa))
  (and
  (= (tb2t29
     (Tuple2 (tuple21 int enum_OBF__aa1) (tuple21 int enum_OBF__aa1)
     (t2tb6 (Tuple21 x y)) (t2tb6 (Tuple21 z a)))) e)
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 z))
  (t2tb22 r1)) (mem (tuple21 enum_OBF__aa1 enum_OBF__aa1)
  (Tuple2 enum_OBF__aa1 enum_OBF__aa1 (t2tb7 y) (t2tb7 a)) (t2tb33 r2))))))))

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
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))) f
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a s (t2tb t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) c)) g
  (infix_plmngt c (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb t) u))
  (and (mem a x (dom (tuple21 (tuple21 int enum_OBF__aa1) int) a f)) (mem2
  (tb2t2 (apply (tuple21 (tuple21 int enum_OBF__aa1) int) a f x))
  (tb2t (dom c (tuple21 (tuple21 int enum_OBF__aa1) int) g))))))
  (= (apply c a (semicolon c (tuple21 (tuple21 int enum_OBF__aa1) int) a f g)
     x) (apply c (tuple21 (tuple21 int enum_OBF__aa1) int) g
        (apply (tuple21 (tuple21 int enum_OBF__aa1) int) a f x)))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb1 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb1 t) u))
  (and (mem a x (dom int a f)) (mem1 (tb2t3 (apply int a f x))
  (tb2t1 (dom c int g))))))
  (= (apply c a (semicolon c int a f g) x) (apply c int g (apply int a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) (g uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (t (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb9 f)
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) (t2tb t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) c)) g
  (infix_plmngt c (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb t) u))
  (and (mem2 x
  (tb2t
  (dom (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f)))) (mem2
  (tb2t2
  (apply (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f) (t2tb2 x)))
  (tb2t (dom c (tuple21 (tuple21 int enum_OBF__aa1) int) g))))))
  (= (apply c (tuple21 (tuple21 int enum_OBF__aa1) int)
     (semicolon c (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f) g) (t2tb2 x)) 
  (apply c (tuple21 (tuple21 int enum_OBF__aa1) int) g
  (apply (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 f) (t2tb2 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (f (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))) (g uni)
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (t2tb12 f)
  (infix_plmngt int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)
  (t2tb1 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb1 t) u))
  (and (mem2 x
  (tb2t (dom int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 f))))
  (mem1
  (tb2t3
  (apply int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 f) (t2tb2 x)))
  (tb2t1 (dom c int g))))))
  (= (apply c (tuple21 (tuple21 int enum_OBF__aa1) int)
     (semicolon c int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 f) g)
     (t2tb2 x)) (apply c int g
                (apply int (tuple21 (tuple21 int enum_OBF__aa1) int)
                (t2tb12 f) (t2tb2 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (f uni) (g uni)
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem2 x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) f)))
  (mem b (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 x))
  (dom c b g)))))
  (= (apply c (tuple21 (tuple21 int enum_OBF__aa1) int)
     (semicolon c b (tuple21 (tuple21 int enum_OBF__aa1) int) f g) (t2tb2 x)) 
  (apply c b g
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))) (g uni) (s (set Int)) (t (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb17 f)
  (infix_plmngt (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 s)
  (t2tb t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) c)) g
  (infix_plmngt c (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb t) u))
  (and (mem1 x
  (tb2t1 (dom (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 f))))
  (mem2
  (tb2t2
  (apply (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 f) (t2tb3 x)))
  (tb2t (dom c (tuple21 (tuple21 int enum_OBF__aa1) int) g))))))
  (= (apply c int
     (semicolon c (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb17 f) g)
     (t2tb3 x)) (apply c (tuple21 (tuple21 int enum_OBF__aa1) int) g
                (apply (tuple21 (tuple21 int enum_OBF__aa1) int) int
                (t2tb17 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int Int))) (g uni) (s (set Int))
  (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int int)) (t2tb22 f)
  (infix_plmngt int int (t2tb1 s) (t2tb1 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb1 t) u))
  (and (mem1 x (tb2t1 (dom int int (t2tb22 f)))) (mem1
  (tb2t3 (apply int int (t2tb22 f) (t2tb3 x))) (tb2t1 (dom c int g))))))
  (= (apply c int (semicolon c int int (t2tb22 f) g) (t2tb3 x)) (apply c 
                                                                int g
                                                                (apply 
                                                                int int
                                                                (t2tb22 f)
                                                                (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x Int) (f uni) (g uni) (s (set Int)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t1 (dom b int f))) (mem b (apply b int f (t2tb3 x))
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
  (forall ((f uni) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_gtmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (=> (mem2 x s)
  (=> (mem2 y s)
  (=>
  (= (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 x)) 
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f (t2tb2 y))) (= x y)))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (forall ((x Int) (y Int))
  (=> (mem (set1 (tuple21 int b)) f (infix_gtmngt b int (t2tb1 s) t))
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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y))
  (id (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)))
  (and (mem2 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
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
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (c Int))
  (=> (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1)
  (t2tb s2) c)
  (=> (mem2 x s2)
  (=> (mem2 x s1) (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))
  (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset int (add int (t2tb3 x) (t2tb1 s1))
  (t2tb1 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (c Int))
  (=> (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1)
  (t2tb s2) c)
  (=> (mem2 x s2)
  (=> (not (mem2 x s1)) (is_finite_subset
  (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))
  (t2tb s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset int (add int (t2tb3 x) (t2tb1 s1))
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
  (forall ((z (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (z1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb z)
  (t2tb z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (and
  (and (= z (tb2t (empty (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1)
  (t2tb s2) c)
  (and (mem2 x s2)
  (and (mem2 x s1)
  (and
  (and
  (= z (tb2t
       (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1)
  (t2tb s2) c)
  (and (mem2 x s2)
  (and (not (mem2 x s1))
  (and
  (and
  (= z (tb2t
       (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb1 z) (t2tb1 z1) z2)
  (or
  (or
  (exists ((s (set Int)))
  (and (and (= z (tb2t1 (empty int))) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1)
  (and (and (= z (tb2t1 (add int (t2tb3 x) (t2tb1 s1)))) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (and (mem1 x s2)
  (and (not (mem1 x s1))
  (and (and (= z (tb2t1 (add int (t2tb3 x) (t2tb1 s1)))) (= z1 s2))
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
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb s1)
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s2)))
  (=> (mem2 x s2) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s2)))))))

(declare-fun t2tb48 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb48 x))))

(declare-fun tb2t48 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t48 (t2tb48 i)) i) :pattern ((t2tb48 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb48 (tb2t48 j)) j) :pattern ((t2tb48 (tb2t48 j))) )))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb1 s1) (finite_subsets int (t2tb1 s2)))
  (=> (mem1 x s2) (mem (set1 int) (add int (t2tb3 x) (t2tb1 s1))
  (finite_subsets int (t2tb1 s2)))))))

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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb s1)
     (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s2)))
     (=> (not (mem2 x s1))
     (= (card (tuple21 (tuple21 int enum_OBF__aa1) int)
        (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))) (+ 
     (card (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1)) 1)))) :pattern ((mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb s1)
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s2)))
  (card (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb1 s1) (finite_subsets int (t2tb1 s2)))
     (=> (not (mem1 x s1))
     (= (card int (add int (t2tb3 x) (t2tb1 s1))) (+ (card int (t2tb1 s1)) 1)))) :pattern ((mem
  (set1 int) (t2tb1 s1) (finite_subsets int (t2tb1 s2)))
  (card int (add int (t2tb3 x) (t2tb1 s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb s1)
     (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s2)))
     (=> (mem2 x s1)
     (= (card (tuple21 (tuple21 int enum_OBF__aa1) int)
        (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1))) 
     (card (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s1))))) :pattern ((mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb s1)
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s2)))
  (card (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb1 s1) (finite_subsets int (t2tb1 s2)))
     (=> (mem1 x s1)
     (= (card int (add int (t2tb3 x) (t2tb1 s1))) (card int (t2tb1 s1))))) :pattern ((mem
  (set1 int) (t2tb1 s1) (finite_subsets int (t2tb1 s2)))
  (card int (add int (t2tb3 x) (t2tb1 s1)))) )))

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
  (forall ((a1 uni) (b (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x uni)
  (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y))
     (times (tuple21 (tuple21 int enum_OBF__aa1) int) a a1 (t2tb b)))
     (and (mem a x a1) (mem2 y b))) :pattern ((mem
  (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y))
  (times (tuple21 (tuple21 int enum_OBF__aa1) int) a a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set Int)) (x uni) (y Int))
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y))
     (times int a a1 (t2tb1 b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb3 y)) (times int a a1 (t2tb1 b)))) ))))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (b (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (mem
     (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y))
     (times (tuple21 (tuple21 int enum_OBF__aa1) int)
     (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb a) (t2tb b)))
     (and (mem2 x a) (mem2 y b))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y))
  (times (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (b (set Int))
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y Int))
  (! (= (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x)
     (t2tb3 y))
     (times int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb a) (t2tb1 b)))
     (and (mem2 x a) (mem1 y b))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y))
  (times int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (b1 uni)
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (! (= (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y)
     (times b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb a) b1))
     (and (mem2 x a) (mem b y b1))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y)
  (times b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set (tuple2 Int enum_OBF__aa))) (b (set Int)) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (! (= (mem2 (Tuple22 x y)
     (tb2t (times int (tuple21 int enum_OBF__aa1) (t2tb15 a) (t2tb1 b))))
     (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 a)) (mem1 y b))) :pattern ((mem2
  (Tuple22 x y)
  (tb2t (times int (tuple21 int enum_OBF__aa1) (t2tb15 a) (t2tb1 b))))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (x Int) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (mem (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
     (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x)
     (t2tb2 y))
     (times (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 a) (t2tb b)))
     (and (mem1 x a) (mem2 y b))) :pattern ((mem
  (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y))
  (times (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set enum_OBF__aa)) (x Int) (y enum_OBF__aa))
  (! (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
     (times enum_OBF__aa1 int (t2tb1 a) (t2tb20 b)))
     (and (mem1 x a) (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 b)))) :pattern ((mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (times enum_OBF__aa1 int (t2tb1 a) (t2tb20 b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set Int)) (x Int) (y Int))
  (! (= (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
     (times int int (t2tb1 a) (t2tb1 b))) (and (mem1 x a) (mem1 y b))) :pattern ((mem
  (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y))
  (times int int (t2tb1 a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set Int)) (b1 uni) (x Int) (y uni))
  (! (= (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y)
     (times b int (t2tb1 a) b1)) (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 int b) (Tuple2 int b (t2tb3 x) y) (times b int (t2tb1 a) b1))) ))))

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
  (forall ((c (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (= (mem2 c
  (tb2t
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 (Tuple22 x y))
  (t2tb s)))) (or (= c (Tuple22 x y)) (mem2 c s)))))

;; break_mem_in_add
  (assert
  (forall ((c (tuple2 Int enum_OBF__aa)) (s (set (tuple2 Int enum_OBF__aa)))
  (x Int) (y enum_OBF__aa))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 c)
  (add (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 s)))
  (or (= c (Tuple21 x y)) (mem (tuple21 int enum_OBF__aa1) (t2tb6 c)
  (t2tb15 s))))))

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
  (forall ((r uni) (u uni) (v (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (and
  (=> (subset (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int)) r
  (times (tuple21 (tuple21 int enum_OBF__aa1) int) a u (t2tb v)))
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r)
  (and (mem a x u) (mem2 y v)))))
  (=>
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r)
  (and (mem a x u) (mem2 y v))))) (subset
  (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int)) r
  (times (tuple21 (tuple21 int enum_OBF__aa1) int) a u (t2tb v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set Int)))
  (and
  (=> (subset (tuple21 a int) r (times int a u (t2tb1 v)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)
  (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb3 y)) r)
  (and (mem a x u) (mem1 y v))))) (subset (tuple21 a int) r
  (times int a u (t2tb1 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (u (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (subset
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb9 r)
  (times (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb u) (t2tb v)))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x) (t2tb2 y)) (t2tb9 r))
  (and (mem2 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (u (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (v (set Int)))
  (= (subset (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (t2tb12 r)
  (times int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb u) (t2tb1 v)))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y Int))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb2 x) (t2tb3 y))
  (t2tb12 r)) (and (mem2 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (v uni))
  (and
  (=> (subset (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b) r
  (times b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb u) v))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) r)
  (and (mem2 x u) (mem b y v)))))
  (=>
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) r)
  (and (mem2 x u) (mem b y v))))) (subset
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b) r
  (times b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (u (set (tuple2 Int enum_OBF__aa))) (v (set Int)))
  (= (subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb r)
  (times int (tuple21 int enum_OBF__aa1) (t2tb15 u) (t2tb1 v)))
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (=> (mem2 (Tuple22 x y) r)
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 u)) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (u (set Int)) (v (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (subset (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb17 r)
  (times (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb1 u) (t2tb v)))
  (forall ((x Int) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (=> (mem (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb3 x) (t2tb2 y))
  (t2tb17 r)) (and (mem1 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int enum_OBF__aa))) (u (set Int))
  (v (set enum_OBF__aa)))
  (= (subset (tuple21 int enum_OBF__aa1) (t2tb15 r)
  (times enum_OBF__aa1 int (t2tb1 u) (t2tb20 v)))
  (forall ((x Int) (y enum_OBF__aa))
  (=> (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r))
  (and (mem1 x u) (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int Int))) (u (set Int)) (v (set Int)))
  (= (subset (tuple21 int int) (t2tb22 r)
  (times int int (t2tb1 u) (t2tb1 v)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb3 x) (t2tb3 y)) (t2tb22 r))
  (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set Int)) (v uni))
  (and
  (=> (subset (tuple21 int b) r (times b int (t2tb1 u) v))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r)
  (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) r)
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
  (forall ((b ty))
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (! (=> (sort b y)
     (=> (mem2 x s)
     (= (apply b (tuple21 (tuple21 int enum_OBF__aa1) int)
        (times b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s)
        (add b y (empty b))) (t2tb2 x)) y))) :pattern ((apply b
                                                       (tuple21
                                                       (tuple21 int
                                                       enum_OBF__aa1) 
                                                       int)
                                                       (times b
                                                       (tuple21
                                                       (tuple21 int
                                                       enum_OBF__aa1) 
                                                       int) (t2tb s)
                                                       (add b y (empty b)))
                                                       (t2tb2 x))) ))))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (x Int) (y uni))
  (! (=> (sort b y)
     (=> (mem1 x s)
     (= (apply b int (times b int (t2tb1 s) (add b y (empty b))) (t2tb3 x)) y))) :pattern (
  (apply b int (times b int (t2tb1 s) (add b y (empty b))) (t2tb3 x))) ))))

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
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)) (r uni)
  (f (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb f)
  (ran (tuple21 (tuple21 int enum_OBF__aa1) int) e1 r))
  (= (mem (tuple21 e1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 e1 (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y))
  (range_restriction (tuple21 (tuple21 int enum_OBF__aa1) int) e1 r (t2tb f)))
  (and (mem (tuple21 e1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 e1 (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r) (mem2
  y f)))))))

;; range_restriction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y Int) (r uni) (f (set Int)))
  (=> (subset int (t2tb1 f) (ran int e1 r))
  (= (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y))
  (range_restriction int e1 r (t2tb1 f)))
  (and (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y)) r) (mem1 y f)))))))

;; range_restriction_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int) (r (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (f (set Int)))
  (=> (subset int (t2tb1 f) (ran int (tuple21 int enum_OBF__aa1) (t2tb r)))
  (= (mem2 (Tuple22 x y)
  (tb2t
  (range_restriction int (tuple21 int enum_OBF__aa1) (t2tb r) (t2tb1 f))))
  (and (mem2 (Tuple22 x y) r) (mem1 y f))))))

;; range_restriction_def
  (assert
  (forall ((x Int) (y enum_OBF__aa) (r (set (tuple2 Int enum_OBF__aa)))
  (f (set enum_OBF__aa)))
  (=> (subset enum_OBF__aa1 (t2tb20 f) (ran enum_OBF__aa1 int (t2tb15 r)))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (range_restriction enum_OBF__aa1 int (t2tb15 r) (t2tb20 f)))
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r))
  (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 f)))))))

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
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)) (r uni)
  (f (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem (tuple21 e1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 e1 (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y))
  (range_substraction (tuple21 (tuple21 int enum_OBF__aa1) int) e1 r
  (t2tb f)))
  (and (mem (tuple21 e1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 e1 (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb2 y)) r)
  (not (mem2 y f)))))))

;; range_substraction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y Int) (r uni) (f (set Int)))
  (= (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y))
  (range_substraction int e1 r (t2tb1 f)))
  (and (mem (tuple21 e1 int) (Tuple2 e1 int x (t2tb3 y)) r) (not (mem1 y f)))))))

;; range_substraction_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int) (r (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (f (set Int)))
  (= (mem2 (Tuple22 x y)
  (tb2t
  (range_substraction int (tuple21 int enum_OBF__aa1) (t2tb r) (t2tb1 f))))
  (and (mem2 (Tuple22 x y) r) (not (mem1 y f))))))

;; range_substraction_def
  (assert
  (forall ((x Int) (y enum_OBF__aa) (r (set (tuple2 Int enum_OBF__aa)))
  (f (set enum_OBF__aa)))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (range_substraction enum_OBF__aa1 int (t2tb15 r) (t2tb20 f)))
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r))
  (not (mem enum_OBF__aa1 (t2tb7 y) (t2tb20 f)))))))

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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni) (r uni)
  (f (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) e2)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) e2 (t2tb2 x) y)
  (domain_restriction e2 (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb f)
  r))
  (and (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) e2)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) e2 (t2tb2 x) y) r) (mem2
  x f))))))

;; domain_restriction_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int) (r (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (f (set (tuple2 Int enum_OBF__aa))))
  (= (mem2 (Tuple22 x y)
  (tb2t
  (domain_restriction int (tuple21 int enum_OBF__aa1) (t2tb15 f) (t2tb r))))
  (and (mem2 (Tuple22 x y) r) (mem (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (t2tb15 f))))))

;; domain_restriction_def
  (assert
  (forall ((x Int) (y enum_OBF__aa) (r (set (tuple2 Int enum_OBF__aa)))
  (f (set Int)))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (domain_restriction enum_OBF__aa1 int (t2tb1 f) (t2tb15 r)))
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r))
  (mem1 x f)))))

;; domain_restriction_def
  (assert
  (forall ((e2 ty))
  (forall ((x Int) (y uni) (r uni) (f (set Int)))
  (= (mem (tuple21 int e2) (Tuple2 int e2 (t2tb3 x) y)
  (domain_restriction e2 int (t2tb1 f) r))
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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni) (r uni)
  (f (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb f)
  (dom e2 (tuple21 (tuple21 int enum_OBF__aa1) int) r))
  (= (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) e2)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) e2 (t2tb2 x) y)
  (domain_substraction e2 (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb f)
  r))
  (and (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) e2)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) e2 (t2tb2 x) y) r)
  (not (mem2 x f))))))))

;; domain_substraction_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int) (r (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (f (set (tuple2 Int enum_OBF__aa))))
  (=> (subset (tuple21 int enum_OBF__aa1) (t2tb15 f)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb r)))
  (= (mem2 (Tuple22 x y)
  (tb2t
  (domain_substraction int (tuple21 int enum_OBF__aa1) (t2tb15 f) (t2tb r))))
  (and (mem2 (Tuple22 x y) r)
  (not (mem (tuple21 int enum_OBF__aa1) (t2tb6 x) (t2tb15 f))))))))

;; domain_substraction_def
  (assert
  (forall ((x Int) (y enum_OBF__aa) (r (set (tuple2 Int enum_OBF__aa)))
  (f (set Int)))
  (=> (subset int (t2tb1 f) (dom enum_OBF__aa1 int (t2tb15 r)))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (domain_substraction enum_OBF__aa1 int (t2tb1 f) (t2tb15 r)))
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r))
  (not (mem1 x f)))))))

;; domain_substraction_def
  (assert
  (forall ((e2 ty))
  (forall ((x Int) (y uni) (r uni) (f (set Int)))
  (=> (subset int (t2tb1 f) (dom e2 int r))
  (= (mem (tuple21 int e2) (Tuple2 int e2 (t2tb3 x) y)
  (domain_substraction e2 int (t2tb1 f) r))
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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni) (q uni)
  (r uni))
  (= (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y)
  (infix_lspl b (tuple21 (tuple21 int enum_OBF__aa1) int) q r))
  (ite (mem2 x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) r)))
  (mem (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) r) (mem
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb2 x) y) q))))))

;; overriding_def
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int) (q (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (r (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem2 (Tuple22 x y)
  (tb2t (infix_lspl int (tuple21 int enum_OBF__aa1) (t2tb q) (t2tb r))))
  (ite (mem (tuple21 int enum_OBF__aa1) (t2tb6 x)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb r))) (mem2 (Tuple22 x y) r)
  (mem2 (Tuple22 x y) q)))))

;; overriding_def
  (assert
  (forall ((x Int) (y enum_OBF__aa) (q (set (tuple2 Int enum_OBF__aa)))
  (r (set (tuple2 Int enum_OBF__aa))))
  (= (mem (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y))
  (infix_lspl enum_OBF__aa1 int (t2tb15 q) (t2tb15 r)))
  (ite (mem1 x (tb2t1 (dom enum_OBF__aa1 int (t2tb15 r)))) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 r)) (mem
  (tuple21 int enum_OBF__aa1) (t2tb6 (Tuple21 x y)) (t2tb15 q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni) (q uni) (r uni))
  (= (mem (tuple21 int b) (Tuple2 int b (t2tb3 x) y) (infix_lspl b int q r))
  (ite (mem1 x (tb2t1 (dom b int r))) (mem (tuple21 int b)
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
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni) (f uni)
  (g uni) (x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
     (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
     (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) g
     (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t)))
     (=> (mem2 x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) g)))
     (= (apply b (tuple21 (tuple21 int enum_OBF__aa1) int)
        (infix_lspl b (tuple21 (tuple21 int enum_OBF__aa1) int) f g)
        (t2tb2 x)) (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) g
                   (t2tb2 x))))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t)) (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) g
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int)
  (infix_lspl b (tuple21 (tuple21 int enum_OBF__aa1) int) f g) (t2tb2 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t)))
     (=> (mem1 x (tb2t1 (dom b int g)))
     (= (apply b int (infix_lspl b int f g) (t2tb3 x)) (apply b int g
                                                       (t2tb3 x))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t)) (mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t))
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
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (t uni) (f uni)
  (g uni) (x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
     (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
     (mem (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) g
     (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t)))
     (=>
     (not (mem2 x
     (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) g))))
     (=> (mem2 x (tb2t (dom b (tuple21 (tuple21 int enum_OBF__aa1) int) f)))
     (= (apply b (tuple21 (tuple21 int enum_OBF__aa1) int)
        (infix_lspl b (tuple21 (tuple21 int enum_OBF__aa1) int) f g)
        (t2tb2 x)) (apply b (tuple21 (tuple21 int enum_OBF__aa1) int) f
                   (t2tb2 x)))))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) f
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int)
  (infix_lspl b (tuple21 (tuple21 int enum_OBF__aa1) int) f g) (t2tb2 x))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)) g
  (infix_plmngt b (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb s) t))
  (apply b (tuple21 (tuple21 int enum_OBF__aa1) int)
  (infix_lspl b (tuple21 (tuple21 int enum_OBF__aa1) int) f g) (t2tb2 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t)))
     (=> (not (mem1 x (tb2t1 (dom b int g))))
     (=> (mem1 x (tb2t1 (dom b int f)))
     (= (apply b int (infix_lspl b int f g) (t2tb3 x)) (apply b int f
                                                       (t2tb3 x)))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb1 s) t))
  (apply b int (infix_lspl b int f g) (t2tb3 x))) :pattern ((mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb1 s) t))
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

;; set_enum_OBF__aa_axiom
  (assert
  (forall ((x enum_OBF__aa)) (mem enum_OBF__aa1 (t2tb7 x)
  (t2tb20 set_enum_OBF__aa))))

(declare-fun f1 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

(declare-fun t2tb49 ((set (set (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) int))) (t2tb49 x))))

(declare-fun tb2t49 (uni) (set (set (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t49 (t2tb49 i)) i) :pattern ((t2tb49 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb49 (tb2t49 j)) j) :pattern ((t2tb49 (tb2t49 j))) )))

(declare-fun t2tb50 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb50 x))))

(declare-fun tb2t50 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t50 (t2tb50 i)) i) :pattern ((t2tb50 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb50 (tb2t50 j)) j) :pattern ((t2tb50 (tb2t50 j))) )))

(declare-fun t2tb51 ((set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb51 x))))

(declare-fun tb2t51 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t51 (t2tb51 i)) i) :pattern ((t2tb51 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb51 (tb2t51 j)) j) :pattern ((t2tb51 (tb2t51 j))) )))

(declare-fun t2tb52 ((set (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))) (sort
  (set1 (tuple21 (tuple21 int int) int)) (t2tb52 x))))

(declare-fun tb2t52 (uni) (set (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t52 (t2tb52 i)) i) :pattern ((t2tb52 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb52 (tb2t52 j)) j) :pattern ((t2tb52 (tb2t52 j))) )))

;; f1_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f1 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb v_OBF__cccc)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb20 set_enum_OBF__aa))
  (t2tb1 integer)))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb v_OBF__ddcc)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb20 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb v_OBF__eecc)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb20 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb v_OBF__ffcc)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb20 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb v_OBF__jj)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb20 set_enum_OBF__aa))
  (t2tb1 integer))))) (infix_eqeq (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb v_OBF__cccc)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 0) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb7 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb7 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__cc) (empty enum_OBF__aa1))))
  (add int (t2tb3 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb v_OBF__ddcc)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 0) (empty int))
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb7 E_OBF__hh) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb7 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb3 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb v_OBF__eecc)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 1) (empty int))
  (add enum_OBF__aa1 (t2tb7 E_OBF__cc) (empty enum_OBF__aa1)))
  (add int (t2tb3 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb v_OBF__ffcc)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb3 1) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb7 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb7 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__hh) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb7 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb3 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb v_OBF__jj)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb v_OBF__cccc)
  (t2tb v_OBF__ddcc)) (t2tb v_OBF__eecc)) (t2tb v_OBF__ffcc)))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__ggcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb52 v_OBF__hhcc)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)) (t2tb1 v_OBF__eebb)))))
  (mem (set1 (tuple21 int int)) (t2tb22 v_OBF__iicc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__jjcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__kkcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb51 v_OBF__llcc)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__ggcc) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb52 v_OBF__hhcc)
  (add int (t2tb3 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__iicc) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__aabb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__jjcc) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__yy) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__kkcc) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__vv) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__iibb) (empty int)))))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb51 v_OBF__llcc)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)) (t2tb1 v_OBF__eebb))
  (t2tb1 v_OBF__kkbb))))) (mem1 v_OBF__hhbb v_OBF__kkbb)) (mem1 v_OBF__ffbb
  v_OBF__kkbb)) (mem1 v_OBF__aabb v_OBF__kkbb)) (mem1 v_OBF__yy v_OBF__kkbb))
  (mem1 v_OBF__vv v_OBF__kkbb)) (mem1 v_OBF__iibb v_OBF__kkbb))
  (not (= v_OBF__hhbb v_OBF__ffbb))) (not (= v_OBF__hhbb v_OBF__aabb)))
  (not (= v_OBF__hhbb v_OBF__yy))) (not (= v_OBF__hhbb v_OBF__vv)))
  (not (= v_OBF__hhbb v_OBF__iibb))) (not (= v_OBF__ffbb v_OBF__hhbb)))
  (not (= v_OBF__ffbb v_OBF__aabb))) (not (= v_OBF__ffbb v_OBF__yy)))
  (not (= v_OBF__ffbb v_OBF__vv))) (not (= v_OBF__ffbb v_OBF__iibb)))
  (not (= v_OBF__aabb v_OBF__hhbb))) (not (= v_OBF__aabb v_OBF__ffbb)))
  (not (= v_OBF__aabb v_OBF__yy))) (not (= v_OBF__aabb v_OBF__vv)))
  (not (= v_OBF__aabb v_OBF__iibb))) (not (= v_OBF__yy v_OBF__hhbb)))
  (not (= v_OBF__yy v_OBF__ffbb))) (not (= v_OBF__yy v_OBF__aabb)))
  (not (= v_OBF__yy v_OBF__vv))) (not (= v_OBF__yy v_OBF__iibb)))
  (not (= v_OBF__vv v_OBF__hhbb))) (not (= v_OBF__vv v_OBF__ffbb)))
  (not (= v_OBF__vv v_OBF__aabb))) (not (= v_OBF__vv v_OBF__yy)))
  (not (= v_OBF__vv v_OBF__iibb))) (not (= v_OBF__iibb v_OBF__hhbb)))
  (not (= v_OBF__iibb v_OBF__ffbb))) (not (= v_OBF__iibb v_OBF__aabb)))
  (not (= v_OBF__iibb v_OBF__yy))) (not (= v_OBF__iibb v_OBF__vv))) (mem
  (set1 int) (t2tb1 v_OBF__qq) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__qq) (empty int)))) (mem (set1 int)
  (t2tb1 v_OBF__oo) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__oo) (empty int)))) (mem (set1 int)
  (t2tb1 v_OBF__eebb) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__eebb) (empty int)))) (mem (set1 int)
  (t2tb1 v_OBF__kkbb) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__kkbb) (empty int)))))))

(declare-fun f2 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f2_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f2 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and (and (mem1 v_OBF__zzbb v_OBF__qq) (mem1 v_OBF__nn v_OBF__oo)) (mem1
  v_OBF__aacc v_OBF__eebb)) (mem1 v_OBF__bbcc v_OBF__kkbb)))))

(declare-fun f5 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f5_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f5 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 (tuple21 int int)) (t2tb22 v_OBF__ggbb)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb52 v_OBF__ccbb)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)) (t2tb1 v_OBF__eebb)))))
  (mem (set1 (tuple21 int int)) (t2tb22 v_OBF__zz)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__ww)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__mm)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb51 v_OBF__jjbb)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__ggbb) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__hhbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb52 v_OBF__ccbb)
  (add int (t2tb3 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__zz) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__aabb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__ww) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__yy) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb22 v_OBF__mm) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__vv) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)) (t2tb1 v_OBF__eebb))
  (add int (t2tb3 v_OBF__iibb) (empty int)))))) (mem1 v_OBF__tt integer))
  (mem1 v_OBF__kk v_OBF__qq)) (mem1 v_OBF__ll v_OBF__oo)) (mem1 v_OBF__bbbb
  v_OBF__eebb)) (mem1 v_OBF__uu v_OBF__kkbb)) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb51 v_OBF__jjbb)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)) (t2tb1 v_OBF__eebb))
  (t2tb1 v_OBF__kkbb))))) (mem1 v_OBF__mmbb integer)) (mem1 v_OBF__ii
  integer)) (mem2 (Tuple22 (Tuple21 v_OBF__mmbb v_OBF__nnbb) v_OBF__ii)
  v_OBF__jj)) (= v_OBF__oobb v_OBF__tt)) (= v_OBF__ppbb v_OBF__kk))
  (= v_OBF__qqbb v_OBF__ll)) (= v_OBF__rrbb v_OBF__bbbb))
  (= v_OBF__ssbb v_OBF__uu)) (= v_OBF__ttbb v_OBF__llbb)) (infix_eqeq
  (tuple21 int int) (t2tb22 v_OBF__uubb) (t2tb22 v_OBF__ggbb))) (infix_eqeq
  (tuple21 (tuple21 int int) int) (t2tb52 v_OBF__vvbb) (t2tb52 v_OBF__ccbb)))
  (infix_eqeq (tuple21 int int) (t2tb22 v_OBF__wwbb) (t2tb22 v_OBF__zz)))
  (infix_eqeq (tuple21 int int) (t2tb22 v_OBF__xxbb) (t2tb22 v_OBF__ww)))
  (infix_eqeq (tuple21 int int) (t2tb22 v_OBF__yybb) (t2tb22 v_OBF__mm))))))

(declare-fun f12 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f12_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f12 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb v_OBF__jj)
  (infix_plmngt int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int)))
  (t2tb20 set_enum_OBF__aa))
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int)))))
  (infix_eqeq (tuple21 int enum_OBF__aa1)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb v_OBF__jj))
  (times enum_OBF__aa1 int
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int)))
  (t2tb20 set_enum_OBF__aa)))) (mem1 v_OBF__ii
  (tb2t1
  (union int (add int (t2tb3 0) (empty int)) (add int (t2tb3 1) (empty int)))))))))

(declare-fun f14 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f14_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f14 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb) (mem2 (Tuple22 (Tuple21 v_OBF__ii E_OBF__hh) 1)
  v_OBF__jj))))

(declare-fun f15 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

(declare-fun t2tb53 ((tuple2 (tuple2 Int Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int))) (sort
  (tuple21 (tuple21 int int) int) (t2tb53 x))))

(declare-fun tb2t53 (uni) (tuple2 (tuple2 Int Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) Int)))
  (! (= (tb2t53 (t2tb53 i)) i) :pattern ((t2tb53 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb53 (tb2t53 j)) j) :pattern ((t2tb53 (tb2t53 j))) )))

;; f15_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f15 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (=> (= v_OBF__uu v_OBF__hhbb)
  (not (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb22 v_OBF__ggbb))))
  (=> (= v_OBF__uu v_OBF__ffbb)
  (not (mem (tuple21 (tuple21 int int) int)
  (Tuple2 (tuple21 int int) int
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb3 v_OBF__bbbb))
  (t2tb52 v_OBF__ccbb)))))
  (=> (= v_OBF__uu v_OBF__aabb)
  (not (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb22 v_OBF__zz)))))
  (=> (= v_OBF__uu v_OBF__yy)
  (not (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb22 v_OBF__ww)))))
  (=> (= v_OBF__uu v_OBF__vv)
  (not (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb22 v_OBF__mm)))))
  (not (= v_OBF__uu v_OBF__iibb))) (= v_OBF__tt 2)))))

(declare-fun f16 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f16_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f16 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb) (mem2
  (Tuple22 (Tuple21 v_OBF__ii E_OBF__bb) v_OBF__ii) v_OBF__jj))))

(declare-fun f21 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f21_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f21 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb22 v_OBF__zz))
  (mem1 v_OBF__nn v_OBF__oo)) (mem (set1 (tuple21 int int))
  (t2tb22 v_OBF__xx) (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo))))
  (mem (set1 (tuple21 int int)) (t2tb22 v_OBF__pp)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__rr)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__ss)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (= v_OBF__tt 2))
  (= v_OBF__uu v_OBF__aabb)))))

(declare-fun f22 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f22_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f22 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb) (mem2 (Tuple22 (Tuple21 v_OBF__ii E_OBF__cc) 0)
  v_OBF__jj))))

(declare-fun f23 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f23_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f23 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem (tuple21 int int)
  (Tuple2 int int (t2tb3 v_OBF__kk) (t2tb3 v_OBF__ll)) (t2tb22 v_OBF__ww))
  (mem (set1 (tuple21 int int)) (t2tb22 v_OBF__xx)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__pp)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__rr)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (mem
  (set1 (tuple21 int int)) (t2tb22 v_OBF__ss)
  (relation int int (t2tb1 v_OBF__qq) (t2tb1 v_OBF__oo)))) (= v_OBF__tt 2))
  (= v_OBF__uu v_OBF__yy)))))

(declare-fun f24 (Int (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) Int Bool Int Int (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int (set Int) Int (set (tuple2 Int Int)) Int
  (set Int) enum_OBF__aa Int Int (set (tuple2 Int Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) Bool Int (set (tuple2 Int
  Int)) (set Int) Int (set (tuple2 Int Int)) (set (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 Int Int)) Int Int (set (tuple2 (tuple2 Int Int) Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int)) (set (tuple2 (tuple2 Int Int) Int)) Int Int Int Int) Bool)

;; f24_def
  (assert
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (= (f24 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb) (mem2 (Tuple22 (Tuple21 v_OBF__ii E_OBF__dd) 1)
  v_OBF__jj))))

(assert
;; OBF__mmcc_1
 ;; File "POwhy_bpo2why/p9/p9_2.why", line 685, characters 7-18
  (not
  (forall ((v_OBF__zzbb Int) (v_OBF__zz (set (tuple2 Int Int)))
  (v_OBF__yybb (set (tuple2 Int Int))) (v_OBF__yy Int)
  (v_OBF__xxbb (set (tuple2 Int Int))) (v_OBF__xx (set (tuple2 Int Int)))
  (v_OBF__wwbb (set (tuple2 Int Int))) (v_OBF__ww (set (tuple2 Int Int)))
  (v_OBF__vvbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__vv Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu Int) (v_OBF__ttbb Bool)
  (v_OBF__tt Int) (v_OBF__ssbb Int) (v_OBF__ss (set (tuple2 Int Int)))
  (v_OBF__rrbb Int) (v_OBF__rr (set (tuple2 Int Int))) (v_OBF__qqbb Int)
  (v_OBF__qq (set Int)) (v_OBF__ppbb Int) (v_OBF__pp (set (tuple2 Int Int)))
  (v_OBF__oobb Int) (v_OBF__oo (set Int)) (v_OBF__nnbb enum_OBF__aa)
  (v_OBF__nn Int) (v_OBF__mmbb Int) (v_OBF__mm (set (tuple2 Int Int)))
  (v_OBF__llcc (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__llbb Bool) (v_OBF__ll Int) (v_OBF__kkcc (set (tuple2 Int Int)))
  (v_OBF__kkbb (set Int)) (v_OBF__kk Int) (v_OBF__jjcc (set (tuple2 Int
  Int))) (v_OBF__jjbb (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__jj (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int) (v_OBF__ii Int)
  (v_OBF__hhcc (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__hhbb Int)
  (v_OBF__ggcc (set (tuple2 Int Int))) (v_OBF__ggbb (set (tuple2 Int Int)))
  (v_OBF__ffcc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ffbb Int) (v_OBF__eecc (set (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) (v_OBF__eebb (set Int)) (v_OBF__ddcc (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__ddbb (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__cccc (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__ccbb (set (tuple2 (tuple2 Int Int) Int))) (v_OBF__bbcc Int)
  (v_OBF__bbbb Int) (v_OBF__aacc Int) (v_OBF__aabb Int))
  (=>
  (and (f1 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy v_OBF__xxbb v_OBF__xx
  v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv v_OBF__uubb v_OBF__uu
  v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss v_OBF__rrbb v_OBF__rr
  v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp v_OBF__oobb v_OBF__oo
  v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm v_OBF__llcc v_OBF__llbb
  v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk v_OBF__jjcc v_OBF__jjbb
  v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb v_OBF__eecc v_OBF__eebb
  v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb v_OBF__bbcc v_OBF__bbbb
  v_OBF__aacc v_OBF__aabb) (f2 v_OBF__zzbb v_OBF__zz v_OBF__yybb v_OBF__yy
  v_OBF__xxbb v_OBF__xx v_OBF__wwbb v_OBF__ww v_OBF__vvbb v_OBF__vv
  v_OBF__uubb v_OBF__uu v_OBF__ttbb v_OBF__tt v_OBF__ssbb v_OBF__ss
  v_OBF__rrbb v_OBF__rr v_OBF__qqbb v_OBF__qq v_OBF__ppbb v_OBF__pp
  v_OBF__oobb v_OBF__oo v_OBF__nnbb v_OBF__nn v_OBF__mmbb v_OBF__mm
  v_OBF__llcc v_OBF__llbb v_OBF__ll v_OBF__kkcc v_OBF__kkbb v_OBF__kk
  v_OBF__jjcc v_OBF__jjbb v_OBF__jj v_OBF__iicc v_OBF__iibb v_OBF__ii
  v_OBF__hhcc v_OBF__hhbb v_OBF__ggcc v_OBF__ggbb v_OBF__ffcc v_OBF__ffbb
  v_OBF__eecc v_OBF__eebb v_OBF__ddcc v_OBF__ddbb v_OBF__cccc v_OBF__ccbb
  v_OBF__bbcc v_OBF__bbbb v_OBF__aacc v_OBF__aabb)) (mem2
  (Tuple22 (Tuple21 1 E_OBF__hh) 1) v_OBF__jj)))))
(check-sat)
